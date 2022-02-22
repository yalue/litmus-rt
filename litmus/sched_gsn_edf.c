/*
 * litmus/sched_gsn_edf.c
 *
 * Implementation of the GSN-EDF scheduling algorithm.
 *
 * This version uses the simple approach and serializes all scheduling
 * decisions by the use of a queue lock. This is probably not the
 * best way to do it, but it should suffice for now.
 */

#include <linux/spinlock.h>
#include <linux/percpu.h>
#include <linux/sched.h>
#include <linux/sched/signal.h>
#include <linux/sched/topology.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

#include <litmus/debug_trace.h>
#include <litmus/litmus.h>
#include <litmus/jobs.h>
#include <litmus/sched_plugin.h>
#include <litmus/edf_common.h>
#include <litmus/sched_trace.h>
#include <litmus/trace.h>

#include <litmus/preempt.h>
#include <litmus/budget.h>
#include <litmus/np.h>

#include <litmus/bheap.h>

#ifdef CONFIG_SCHED_CPU_AFFINITY
#include <litmus/affinity.h>
#endif

/* to set up domain/cpu mappings */
#include <litmus/litmus_proc.h>

#include <linux/module.h>

// The maximum number of lock holders for the k-FMLP.
#define MAX_KFMLP_K (16)

/* Overview of GSN-EDF operations.
 *
 * For a detailed explanation of GSN-EDF have a look at the FMLP paper. This
 * description only covers how the individual operations are implemented in
 * LITMUS.
 *
 * link_task_to_cpu(T, cpu) 	- Low-level operation to update the linkage
 *                                structure (NOT the actually scheduled
 *                                task). If there is another linked task To
 *                                already it will set To->linked_on = NO_CPU
 *                                (thereby removing its association with this
 *                                CPU). However, it will not requeue the
 *                                previously linked task (if any). It will set
 *                                T's state to not completed and check whether
 *                                it is already running somewhere else. If T
 *                                is scheduled somewhere else it will link
 *                                it to that CPU instead (and pull the linked
 *                                task to cpu). T may be NULL.
 *
 * unlink(T)			- Unlink removes T from all scheduler data
 *                                structures. If it is linked to some CPU it
 *                                will link NULL to that CPU. If it is
 *                                currently queued in the gsnedf queue it will
 *                                be removed from the rt_domain. It is safe to
 *                                call unlink(T) if T is not linked. T may not
 *                                be NULL.
 *
 * requeue(T)			- Requeue will insert T into the appropriate
 *                                queue. If the system is in real-time mode and
 *                                the T is released already, it will go into the
 *                                ready queue. If the system is not in
 *                                real-time mode is T, then T will go into the
 *                                release queue. If T's release time is in the
 *                                future, it will go into the release
 *                                queue. That means that T's release time/job
 *                                no/etc. has to be updated before requeu(T) is
 *                                called. It is not safe to call requeue(T)
 *                                when T is already queued. T may not be NULL.
 *
 * gsnedf_job_arrival(T)	- This is the catch all function when T enters
 *                                the system after either a suspension or at a
 *                                job release. It will queue T (which means it
 *                                is not safe to call gsnedf_job_arrival(T) if
 *                                T is already queued) and then check whether a
 *                                preemption is necessary. If a preemption is
 *                                necessary it will update the linkage
 *                                accordingly and cause scheduled to be called
 *                                (either with an IPI or need_resched). It is
 *                                safe to call gsnedf_job_arrival(T) if T's
 *                                next job has not been actually released yet
 *                                (releast time in the future). T will be put
 *                                on the release queue in that case.
 *
 * curr_job_completion()	- Take care of everything that needs to be done
 *                                to prepare the current task for its next
 *                                release and place it in the right queue with
 *                                gsnedf_job_arrival().
 *
 *
 * When we now that T is linked to CPU then link_task_to_cpu(NULL, CPU) is
 * equivalent to unlink(T). Note that if you unlink a task from a CPU none of
 * the functions will automatically propagate pending task from the ready queue
 * to a linked task. This is the job of the calling function ( by means of
 * __take_ready).
 */


/* cpu_entry_t - maintain the linked and scheduled state
 */
typedef struct  {
	int 			cpu;
	struct task_struct*	linked;		/* only RT tasks */
	struct task_struct*	scheduled;	/* only RT tasks */
	struct bheap_node*	hn;
} cpu_entry_t;
DEFINE_PER_CPU(cpu_entry_t, gsnedf_cpu_entries);

cpu_entry_t* gsnedf_cpus[NR_CPUS];

/* the cpus queue themselves according to priority in here */
static struct bheap_node gsnedf_heap_node[NR_CPUS];
static struct bheap      gsnedf_cpu_heap;

static rt_domain_t gsnedf;
#define gsnedf_lock (gsnedf.ready_lock)


/* Uncomment this if you want to see all scheduling decisions in the
 * TRACE() log.
#define WANT_ALL_SCHED_EVENTS
 */

static int cpu_lower_prio(struct bheap_node *_a, struct bheap_node *_b)
{
	cpu_entry_t *a, *b;
	a = _a->value;
	b = _b->value;
	/* Note that a and b are inverted: we want the lowest-priority CPU at
	 * the top of the heap.
	 */
	return edf_higher_prio(b->linked, a->linked);
}

/* update_cpu_position - Move the cpu entry to the correct place to maintain
 *                       order in the cpu queue. Caller must hold gsnedf lock.
 */
static void update_cpu_position(cpu_entry_t *entry)
{
	if (likely(bheap_node_in_heap(entry->hn)))
		bheap_delete(cpu_lower_prio, &gsnedf_cpu_heap, entry->hn);
	bheap_insert(cpu_lower_prio, &gsnedf_cpu_heap, entry->hn);
}

/* caller must hold gsnedf lock */
static cpu_entry_t* lowest_prio_cpu(void)
{
	struct bheap_node* hn;
	hn = bheap_peek(cpu_lower_prio, &gsnedf_cpu_heap);
	return hn->value;
}


/* link_task_to_cpu - Update the link of a CPU.
 *                    Handles the case where the to-be-linked task is already
 *                    scheduled on a different CPU.
 */
static noinline void link_task_to_cpu(struct task_struct* linked,
				      cpu_entry_t *entry)
{
	cpu_entry_t *sched;
	struct task_struct* tmp;
	int on_cpu;

	BUG_ON(linked && !is_realtime(linked));

	/* Currently linked task is set to be unlinked. */
	if (entry->linked) {
		entry->linked->rt_param.linked_on = NO_CPU;
	}

	/* Link new task to CPU. */
	if (linked) {
		/* handle task is already scheduled somewhere! */
		on_cpu = linked->rt_param.scheduled_on;
		if (on_cpu != NO_CPU) {
			sched = &per_cpu(gsnedf_cpu_entries, on_cpu);
			/* this should only happen if not linked already */
			BUG_ON(sched->linked == linked);

			/* If we are already scheduled on the CPU to which we
			 * wanted to link, we don't need to do the swap --
			 * we just link ourselves to the CPU and depend on
			 * the caller to get things right.
			 */
			if (entry != sched) {
				TRACE_TASK(linked,
					   "already scheduled on %d, updating link.\n",
					   sched->cpu);
				tmp = sched->linked;
				linked->rt_param.linked_on = sched->cpu;
				sched->linked = linked;
				update_cpu_position(sched);
				linked = tmp;
			}
		}
		if (linked) /* might be NULL due to swap */
			linked->rt_param.linked_on = entry->cpu;
	}
	entry->linked = linked;
#ifdef WANT_ALL_SCHED_EVENTS
	if (linked)
		TRACE_TASK(linked, "linked to %d.\n", entry->cpu);
	else
		TRACE("NULL linked to %d.\n", entry->cpu);
#endif
	update_cpu_position(entry);
}

/* unlink - Make sure a task is not linked any longer to an entry
 *          where it was linked before. Must hold gsnedf_lock.
 */
static noinline void unlink(struct task_struct* t)
{
	cpu_entry_t *entry;

	if (t->rt_param.linked_on != NO_CPU) {
		/* unlink */
		entry = &per_cpu(gsnedf_cpu_entries, t->rt_param.linked_on);
		t->rt_param.linked_on = NO_CPU;
		link_task_to_cpu(NULL, entry);
	} else if (is_queued(t)) {
		/* This is an interesting situation: t is scheduled,
		 * but was just recently unlinked.  It cannot be
		 * linked anywhere else (because then it would have
		 * been relinked to this CPU), thus it must be in some
		 * queue. We must remove it from the list in this
		 * case.
		 */
		remove(&gsnedf, t);
	}
}


/* preempt - force a CPU to reschedule
 */
static void preempt(cpu_entry_t *entry)
{
	preempt_if_preemptable(entry->scheduled, entry->cpu);
}

/* requeue - Put an unlinked task into gsn-edf domain.
 *           Caller must hold gsnedf_lock.
 */
static noinline void requeue(struct task_struct* task)
{
	BUG_ON(!task);
	/* sanity check before insertion */
	BUG_ON(is_queued(task));

	if (is_early_releasing(task) || is_released(task, litmus_clock()))
		__add_ready(&gsnedf, task);
	else {
		/* it has got to wait */
		add_release(&gsnedf, task);
	}
}

#ifdef CONFIG_SCHED_CPU_AFFINITY
static cpu_entry_t* gsnedf_get_nearest_available_cpu(cpu_entry_t *start)
{
	cpu_entry_t *affinity;

	get_nearest_available_cpu(affinity, start, gsnedf_cpu_entries,
#ifdef CONFIG_RELEASE_MASTER
			gsnedf.release_master,
#else
			NO_CPU,
#endif
			cpu_online_mask);

	return(affinity);
}
#endif

/* check for any necessary preemptions */
static void check_for_preemptions(void)
{
	struct task_struct *task;
	cpu_entry_t *last;


#ifdef CONFIG_PREFER_LOCAL_LINKING
	cpu_entry_t *local;

	/* Before linking to other CPUs, check first whether the local CPU is
	 * idle. */
	local = this_cpu_ptr(&gsnedf_cpu_entries);
	task  = __peek_ready(&gsnedf);

	if (task && !local->linked
#ifdef CONFIG_RELEASE_MASTER
	    && likely(local->cpu != gsnedf.release_master)
#endif
		) {
		task = __take_ready(&gsnedf);
		TRACE_TASK(task, "linking to local CPU %d to avoid IPI\n", local->cpu);
		link_task_to_cpu(task, local);
		preempt(local);
	}
#endif

	for (last = lowest_prio_cpu();
	     edf_preemption_needed(&gsnedf, last->linked);
	     last = lowest_prio_cpu()) {
		/* preemption necessary */
		task = __take_ready(&gsnedf);
		TRACE("check_for_preemptions: attempting to link task %d to %d\n",
		      task->pid, last->cpu);

#ifdef CONFIG_SCHED_CPU_AFFINITY
		{
			cpu_entry_t *affinity =
					gsnedf_get_nearest_available_cpu(
						&per_cpu(gsnedf_cpu_entries, task_cpu(task)));
			if (affinity)
				last = affinity;
			else if (requeue_preempted_job(last->linked))
				requeue(last->linked);
		}
#else
		if (requeue_preempted_job(last->linked))
			requeue(last->linked);
#endif

		link_task_to_cpu(task, last);
		preempt(last);
	}
}

/* gsnedf_job_arrival: task is either resumed or released */
static noinline void gsnedf_job_arrival(struct task_struct* task)
{
	BUG_ON(!task);

	requeue(task);
	check_for_preemptions();
}

static void gsnedf_release_jobs(rt_domain_t* rt, struct bheap* tasks)
{
	unsigned long flags;

	raw_spin_lock_irqsave(&gsnedf_lock, flags);

	__merge_ready(rt, tasks);
	check_for_preemptions();

	raw_spin_unlock_irqrestore(&gsnedf_lock, flags);
}

/* caller holds gsnedf_lock */
static noinline void curr_job_completion(int forced)
{
	struct task_struct *t = current;
	BUG_ON(!t);

	sched_trace_task_completion(t, forced);

	TRACE_TASK(t, "job_completion(forced=%d).\n", forced);

	/* set flags */
	tsk_rt(t)->completed = 0;
	/* prepare for next period */
	prepare_for_next_period(t);
	if (is_early_releasing(t) || is_released(t, litmus_clock()))
		sched_trace_task_release(t);
	/* unlink */
	unlink(t);
	/* requeue
	 * But don't requeue a blocking task. */
	if (is_current_running())
		gsnedf_job_arrival(t);
}

/* Getting schedule() right is a bit tricky. schedule() may not make any
 * assumptions on the state of the current task since it may be called for a
 * number of reasons. The reasons include a scheduler_tick() determined that it
 * was necessary, because sys_exit_np() was called, because some Linux
 * subsystem determined so, or even (in the worst case) because there is a bug
 * hidden somewhere. Thus, we must take extreme care to determine what the
 * current state is.
 *
 * The CPU could currently be scheduling a task (or not), be linked (or not).
 *
 * The following assertions for the scheduled task could hold:
 *
 *      - !is_running(scheduled)        // the job blocks
 *	- scheduled->timeslice == 0	// the job completed (forcefully)
 *	- is_completed()		// the job completed (by syscall)
 * 	- linked != scheduled		// we need to reschedule (for any reason)
 * 	- is_np(scheduled)		// rescheduling must be delayed,
 *					   sys_exit_np must be requested
 *
 * Any of these can occur together.
 */
static struct task_struct* gsnedf_schedule(struct task_struct * prev)
{
	cpu_entry_t* entry = this_cpu_ptr(&gsnedf_cpu_entries);
	int out_of_time, sleep, preempt, np, exists, blocks;
	struct task_struct* next = NULL;

#ifdef CONFIG_RELEASE_MASTER
	/* Bail out early if we are the release master.
	 * The release master never schedules any real-time tasks.
	 */
	if (unlikely(gsnedf.release_master == entry->cpu)) {
		sched_state_task_picked();
		return NULL;
	}
#endif

	raw_spin_lock(&gsnedf_lock);

	/* sanity checking */
	BUG_ON(entry->scheduled && entry->scheduled != prev);
	BUG_ON(entry->scheduled && !is_realtime(prev));
	BUG_ON(is_realtime(prev) && !entry->scheduled);

	/* (0) Determine state */
	exists      = entry->scheduled != NULL;
	blocks      = exists && !is_current_running();
	out_of_time = exists && budget_enforced(entry->scheduled)
		&& budget_exhausted(entry->scheduled);
	np 	    = exists && is_np(entry->scheduled);
	sleep	    = exists && is_completed(entry->scheduled);
	preempt     = entry->scheduled != entry->linked;

#ifdef WANT_ALL_SCHED_EVENTS
	TRACE_TASK(prev, "invoked gsnedf_schedule.\n");
#endif

	if (exists)
		TRACE_TASK(prev,
			   "blocks:%d out_of_time:%d np:%d sleep:%d preempt:%d "
			   "state:%d sig:%d\n",
			   blocks, out_of_time, np, sleep, preempt,
			   READ_ONCE(prev->__state), signal_pending(prev));
	if (entry->linked && preempt)
		TRACE_TASK(prev, "will be preempted by %s/%d\n",
			   entry->linked->comm, entry->linked->pid);


	/* If a task blocks we have no choice but to reschedule.
	 */
	if (blocks)
		unlink(entry->scheduled);

	/* Request a sys_exit_np() call if we would like to preempt but cannot.
	 * We need to make sure to update the link structure anyway in case
	 * that we are still linked. Multiple calls to request_exit_np() don't
	 * hurt.
	 */
	if (np && (out_of_time || preempt || sleep)) {
		unlink(entry->scheduled);
		request_exit_np(entry->scheduled);
	}

	/* Any task that is preemptable and either exhausts its execution
	 * budget or wants to sleep completes. We may have to reschedule after
	 * this. Don't do a job completion if we block (can't have timers running
	 * for blocked jobs).
	 */
	if (!np && (out_of_time || sleep))
		curr_job_completion(!sleep);

	/* Link pending task if we became unlinked.
	 */
	if (!entry->linked)
		link_task_to_cpu(__take_ready(&gsnedf), entry);

	/* The final scheduling decision. Do we need to switch for some reason?
	 * If linked is different from scheduled, then select linked as next.
	 */
	if ((!np || blocks) &&
	    entry->linked != entry->scheduled) {
		/* Schedule a linked job? */
		if (entry->linked) {
			entry->linked->rt_param.scheduled_on = entry->cpu;
			next = entry->linked;
			TRACE_TASK(next, "scheduled_on = P%d\n", smp_processor_id());
		}
		if (entry->scheduled) {
			/* not gonna be scheduled soon */
			entry->scheduled->rt_param.scheduled_on = NO_CPU;
			TRACE_TASK(entry->scheduled, "scheduled_on = NO_CPU\n");
		}
	} else
		/* Only override Linux scheduler if we have a real-time task
		 * scheduled that needs to continue.
		 */
		if (exists)
			next = prev;

	sched_state_task_picked();

	raw_spin_unlock(&gsnedf_lock);

#ifdef WANT_ALL_SCHED_EVENTS
	TRACE("gsnedf_lock released, next=0x%p\n", next);

	if (next)
		TRACE_TASK(next, "scheduled at %llu\n", litmus_clock());
	else if (exists && !next)
		TRACE("becomes idle at %llu.\n", litmus_clock());
#endif


	return next;
}


/* _finish_switch - we just finished the switch away from prev
 */
static void gsnedf_finish_switch(struct task_struct *prev)
{
	cpu_entry_t* 	entry = this_cpu_ptr(&gsnedf_cpu_entries);

	entry->scheduled = is_realtime(current) ? current : NULL;
#ifdef WANT_ALL_SCHED_EVENTS
	TRACE_TASK(prev, "switched away from\n");
#endif
}


/*	Prepare a task for running in RT mode
 */
static void gsnedf_task_new(struct task_struct * t, int on_rq, int is_scheduled)
{
	unsigned long 		flags;
	cpu_entry_t* 		entry;

	TRACE("gsn edf: task new %d\n", t->pid);

	raw_spin_lock_irqsave(&gsnedf_lock, flags);

	/* setup job params */
	release_at(t, litmus_clock());

	if (is_scheduled) {
		entry = &per_cpu(gsnedf_cpu_entries, task_cpu(t));
		BUG_ON(entry->scheduled);

#ifdef CONFIG_RELEASE_MASTER
		if (entry->cpu != gsnedf.release_master) {
#endif
			entry->scheduled = t;
			tsk_rt(t)->scheduled_on = task_cpu(t);
#ifdef CONFIG_RELEASE_MASTER
		} else {
			/* do not schedule on release master */
			preempt(entry); /* force resched */
			tsk_rt(t)->scheduled_on = NO_CPU;
		}
#endif
	} else {
		t->rt_param.scheduled_on = NO_CPU;
	}
	t->rt_param.linked_on          = NO_CPU;

	if (on_rq || is_scheduled)
		gsnedf_job_arrival(t);
	raw_spin_unlock_irqrestore(&gsnedf_lock, flags);
}

static void gsnedf_task_wake_up(struct task_struct *task)
{
	unsigned long flags;
	lt_t now;

	TRACE_TASK(task, "wake_up at %llu\n", litmus_clock());

	raw_spin_lock_irqsave(&gsnedf_lock, flags);
	now = litmus_clock();
	if (is_sporadic(task) && is_tardy(task, now)) {
		inferred_sporadic_job_release_at(task, now);
	}
	gsnedf_job_arrival(task);
	raw_spin_unlock_irqrestore(&gsnedf_lock, flags);
}

static void gsnedf_task_block(struct task_struct *t)
{
	unsigned long flags;

	TRACE_TASK(t, "block at %llu\n", litmus_clock());

	/* unlink if necessary */
	raw_spin_lock_irqsave(&gsnedf_lock, flags);
	unlink(t);
	raw_spin_unlock_irqrestore(&gsnedf_lock, flags);

	BUG_ON(!is_realtime(t));
}


static void gsnedf_task_exit(struct task_struct * t)
{
	unsigned long flags;

	/* unlink if necessary */
	raw_spin_lock_irqsave(&gsnedf_lock, flags);
	unlink(t);
	if (tsk_rt(t)->scheduled_on != NO_CPU) {
		gsnedf_cpus[tsk_rt(t)->scheduled_on]->scheduled = NULL;
		tsk_rt(t)->scheduled_on = NO_CPU;
	}
	raw_spin_unlock_irqrestore(&gsnedf_lock, flags);

	BUG_ON(!is_realtime(t));
        TRACE_TASK(t, "RIP\n");
}


static long gsnedf_admit_task(struct task_struct* tsk)
{
	return 0;
}

#ifdef CONFIG_LITMUS_LOCKING

#include <litmus/fdso.h>

/* called with IRQs off */
static void set_priority_inheritance(struct task_struct* t, struct task_struct* prio_inh)
{
	int linked_on;
	int check_preempt = 0;

	raw_spin_lock(&gsnedf_lock);

	TRACE_TASK(t, "inherits priority from %s/%d\n", prio_inh->comm, prio_inh->pid);
	tsk_rt(t)->inh_task = prio_inh;

	linked_on  = tsk_rt(t)->linked_on;

	/* If it is scheduled, then we need to reorder the CPU heap. */
	if (linked_on != NO_CPU) {
		TRACE_TASK(t, "%s: linked  on %d\n",
			   __FUNCTION__, linked_on);
		/* Holder is scheduled; need to re-order CPUs.
		 * We can't use heap_decrease() here since
		 * the cpu_heap is ordered in reverse direction, so
		 * it is actually an increase. */
		bheap_delete(cpu_lower_prio, &gsnedf_cpu_heap,
			    gsnedf_cpus[linked_on]->hn);
		bheap_insert(cpu_lower_prio, &gsnedf_cpu_heap,
			    gsnedf_cpus[linked_on]->hn);
	} else {
		/* holder may be queued: first stop queue changes */
		raw_spin_lock(&gsnedf.release_lock);
		if (is_queued(t)) {
			TRACE_TASK(t, "%s: is queued\n",
				   __FUNCTION__);
			/* We need to update the position of holder in some
			 * heap. Note that this could be a release heap if we
			 * budget enforcement is used and this job overran. */
			check_preempt =
				!bheap_decrease(edf_ready_order,
					       tsk_rt(t)->heap_node);
		} else {
			/* Nothing to do: if it is not queued and not linked
			 * then it is either sleeping or currently being moved
			 * by other code (e.g., a timer interrupt handler) that
			 * will use the correct priority when enqueuing the
			 * task. */
			TRACE_TASK(t, "%s: is NOT queued => Done.\n",
				   __FUNCTION__);
		}
		raw_spin_unlock(&gsnedf.release_lock);

		/* If holder was enqueued in a release heap, then the following
		 * preemption check is pointless, but we can't easily detect
		 * that case. If you want to fix this, then consider that
		 * simply adding a state flag requires O(n) time to update when
		 * releasing n tasks, which conflicts with the goal to have
		 * O(log n) merges. */
		if (check_preempt) {
			/* heap_decrease() hit the top level of the heap: make
			 * sure preemption checks get the right task, not the
			 * potentially stale cache. */
			bheap_uncache_min(edf_ready_order,
					 &gsnedf.ready_queue);
			check_for_preemptions();
		}
	}

	raw_spin_unlock(&gsnedf_lock);
}

/* called with IRQs off */
static void clear_priority_inheritance(struct task_struct* t)
{
	raw_spin_lock(&gsnedf_lock);

	/* A job only stops inheriting a priority when it releases a
	 * resource. Thus we can make the following assumption.*/
	BUG_ON(tsk_rt(t)->scheduled_on == NO_CPU);

	TRACE_TASK(t, "priority restored\n");
	tsk_rt(t)->inh_task = NULL;

	/* Check if rescheduling is necessary. We can't use heap_decrease()
	 * since the priority was effectively lowered. */
	unlink(t);
	gsnedf_job_arrival(t);

	raw_spin_unlock(&gsnedf_lock);
}


/* ******************** FMLP support ********************** */

/* struct for semaphore with priority inheritance */
struct fmlp_semaphore {
	struct litmus_lock litmus_lock;

	/* current resource holder */
	struct task_struct *owner;

	/* highest-priority waiter */
	struct task_struct *hp_waiter;

	/* FIFO queue of waiting tasks */
	wait_queue_head_t wait;
};

static inline struct fmlp_semaphore* fmlp_from_lock(struct litmus_lock* lock)
{
	return container_of(lock, struct fmlp_semaphore, litmus_lock);
}

/* caller is responsible for locking */
struct task_struct* find_hp_waiter(struct fmlp_semaphore *sem,
				   struct task_struct* skip)
{
	struct list_head	*pos;
	struct task_struct	*queued, *found = NULL;

	list_for_each(pos, &sem->wait.head) {
		queued  = (struct task_struct*) list_entry(pos,
							   wait_queue_entry_t,
							   entry)->private;

		/* Compare task prios, find high prio task. */
		if (queued != skip && edf_higher_prio(queued, found))
			found = queued;
	}
	return found;
}

int gsnedf_fmlp_lock(struct litmus_lock* l)
{
	struct task_struct* t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	wait_queue_entry_t wait;
	unsigned long flags;

	if (!is_realtime(t))
		return -EPERM;

	/* prevent nested lock acquisition --- not supported by FMLP */
	if (tsk_rt(t)->num_locks_held)
		return -EBUSY;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner) {
		/* resource is not free => must suspend and wait */

		init_waitqueue_entry(&wait, t);

		/* FIXME: interruptible would be nice some day */
		set_current_state(TASK_UNINTERRUPTIBLE);

		__add_wait_queue_entry_tail_exclusive(&sem->wait, &wait);

		/* check if we need to activate priority inheritance */
		if (edf_higher_prio(t, sem->hp_waiter)) {
			sem->hp_waiter = t;
			if (edf_higher_prio(t, sem->owner))
				set_priority_inheritance(sem->owner, sem->hp_waiter);
		}

		TS_LOCK_SUSPEND;

		/* release lock before sleeping */
		spin_unlock_irqrestore(&sem->wait.lock, flags);

		/* We depend on the FIFO order.  Thus, we don't need to recheck
		 * when we wake up; we are guaranteed to have the lock since
		 * there is only one wake up per release.
		 */

		schedule();

		TS_LOCK_RESUME;

		/* Since we hold the lock, no other task will change
		 * ->owner. We can thus check it without acquiring the spin
		 * lock. */
		BUG_ON(sem->owner != t);
	} else {
		/* it's ours now */
		sem->owner = t;

		spin_unlock_irqrestore(&sem->wait.lock, flags);
	}

	tsk_rt(t)->num_locks_held++;

	return 0;
}

int gsnedf_fmlp_unlock(struct litmus_lock* l)
{
	struct task_struct *t = current, *next;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;
	int err = 0;

	spin_lock_irqsave(&sem->wait.lock, flags);

	if (sem->owner != t) {
		err = -EINVAL;
		goto out;
	}

	tsk_rt(t)->num_locks_held--;

	/* check if there are jobs waiting for this resource */
	next = __waitqueue_remove_first(&sem->wait);
	if (next) {
		/* next becomes the resouce holder */
		sem->owner = next;
		TRACE_CUR("lock ownership passed to %s/%d\n", next->comm, next->pid);

		/* determine new hp_waiter if necessary */
		if (next == sem->hp_waiter) {
			TRACE_TASK(next, "was highest-prio waiter\n");
			/* next has the highest priority --- it doesn't need to
			 * inherit.  However, we need to make sure that the
			 * next-highest priority in the queue is reflected in
			 * hp_waiter. */
			sem->hp_waiter = find_hp_waiter(sem, next);
			if (sem->hp_waiter)
				TRACE_TASK(sem->hp_waiter, "is new highest-prio waiter\n");
			else
				TRACE("no further waiters\n");
		} else {
			/* Well, if next is not the highest-priority waiter,
			 * then it ought to inherit the highest-priority
			 * waiter's priority. */
			set_priority_inheritance(next, sem->hp_waiter);
		}

		/* wake up next */
		wake_up_process(next);
	} else
		/* becomes available */
		sem->owner = NULL;

	/* we lose the benefit of priority inheritance (if any) */
	if (tsk_rt(t)->inh_task)
		clear_priority_inheritance(t);

out:
	spin_unlock_irqrestore(&sem->wait.lock, flags);

	return err;
}

int gsnedf_fmlp_close(struct litmus_lock* l)
{
	struct task_struct *t = current;
	struct fmlp_semaphore *sem = fmlp_from_lock(l);
	unsigned long flags;

	int owner;

	spin_lock_irqsave(&sem->wait.lock, flags);

	owner = sem->owner == t;

	spin_unlock_irqrestore(&sem->wait.lock, flags);

	if (owner)
		gsnedf_fmlp_unlock(l);

	return 0;
}

void gsnedf_fmlp_free(struct litmus_lock* lock)
{
	kfree(fmlp_from_lock(lock));
}

static struct litmus_lock_ops gsnedf_fmlp_lock_ops = {
	.close  = gsnedf_fmlp_close,
	.lock   = gsnedf_fmlp_lock,
	.unlock = gsnedf_fmlp_unlock,
	.deallocate = gsnedf_fmlp_free,
};

static struct litmus_lock* gsnedf_new_fmlp(void)
{
	struct fmlp_semaphore* sem;

	sem = kmalloc(sizeof(*sem), GFP_KERNEL);
	if (!sem)
		return NULL;

	sem->owner   = NULL;
	sem->hp_waiter = NULL;
	init_waitqueue_head(&sem->wait);
	sem->litmus_lock.ops = &gsnedf_fmlp_lock_ops;

	return &sem->litmus_lock;
}

// Unlike with regular FMLP it may not be obvious which lock owner is receiving
// priority donation, so here we'll keep track of who's donating to who.
struct kfmlp_hp_waiter {
	struct task_struct *waiter;
	// The index, in the owners array, of the task receiving the donation.
	// -1 if not currently donating priority.
	int donee_index;
};

/* For Nathan's k-FMLP locks */
struct kfmlp_semaphore {
	struct litmus_lock litmus_lock;

	// The number of owners this lock may have.
	int k;

	// The list of lock holders. At most the first k will be used, and will
	// be NULL if available.
	struct task_struct *owners[MAX_KFMLP_K];

	// The list of up to k highest-priority waiters. Only the first k
	// entries in this will be used.
	//
	// TODO: Replace this with a sorted list, kept sorted on insert/removal
	struct kfmlp_hp_waiter hp_waiters[MAX_KFMLP_K];

	// The index of the lowest-priority of the hp_waiters.
	int lowest_hp_waiter;

	// The total number of waiters in the lock's wait queue.
	int num_waiters;

	/* FIFO queue of waiting tasks */
	wait_queue_head_t wait;
};

static inline struct kfmlp_semaphore* kfmlp_from_lock(struct litmus_lock* lock)
{
	return container_of(lock, struct kfmlp_semaphore, litmus_lock);
}


static void gsnedf_kfmlp_free(struct litmus_lock* lock)
{
	struct kfmlp_semaphore *sem = kfmlp_from_lock(lock);
	kfree(sem);
}

// Returns the index of the first free non-held slot in the lock. Returns -1 if
// all slots are occupied.
static int kfmlp_get_free_slot_index(struct kfmlp_semaphore *sem)
{
	int i = 0;
	for (i = 0; i < sem->k; i++) {
		if (!sem->owners[i]) return i;
	}
	return -1;
}

// Returns nonzero if we actually have been assigned a slot in the given
// k-exclusion lock. Returns zero otherwise. Used to check whether we were
// woken up due to holding a lock or whether we were just spuriously woken up.
// Trusts the control page.
static int verify_kfmlp_ownership(struct kfmlp_semaphore *sem)
{
	struct task_struct *t = current;
	// Side note, this shouldn't have been trashed by the user process, as
	// the task should have remained suspended or in kernel code prior to
	// this check.
	int slot = tsk_rt(t)->ctrl_page->k_exclusion_slot;
	if (slot > ((uint64_t) sem->k)) return 0;
	return sem->owners[slot] == t;
}

// Returns a non-negative value, indicating current's slot in sem->owners, if
// current is a lock owner. Doesn't trust the control page.
static int kfmlp_get_owner_slot(struct kfmlp_semaphore *sem)
{
	struct task_struct *t = current;
	int i;
	for (i = 0; i < sem->k; i++) {
		if (sem->owners[i] == t) return i;
	}
	return -1;
}

// Returns the index (between 0 and k - 1, inclusive) of the lock owner with
// the highest priority, so long as it has lower priority than t. Returns -1 if
// none of the lock owners have lower priority than t.
// TODO: Reexamine find_highest_lp_owner. May be good to boost the lowest non-
// boosted owner instead.
static int kfmlp_find_highest_lp_owner(struct kfmlp_semaphore *sem,
	struct task_struct *t)
{
	struct task_struct *candidate = NULL;
	struct task_struct *owner = NULL;
	int to_return = -1;
	int i;
	for (i = 0; i < sem->k; i++) {
		owner = sem->owners[i];
		if (!owner) continue;
		// Ignore tasks that are already inheriting priority from
		// something else.
		if (tsk_rt(owner)->inh_task) continue;
		// Ignore tasks that are already higher priority than t.
		if (edf_higher_prio(owner, t)) continue;
		if (!candidate) {
			// This is the first task we've seen with lower
			// priority.
			candidate = owner;
			to_return = i;
			continue;
		}
		// Ignore this task if we've already seen one that's higher
		// priority.
		if (edf_higher_prio(candidate, owner)) continue;
		// We've found the next highest-priority lower-priority task.
		candidate = sem->owners[i];
		to_return = i;
	}
	return to_return;
}

// Takes the index into the hp_waiters array and checks whether the
// corresponding highest-priority waiter needs to donate priority to anything,
// or updates the priority if there was already a donee and the waiter changed.
static void kfmlp_check_hp_waiter_inheritance(struct kfmlp_semaphore *sem,
	int i)
{
	struct task_struct *waiter = sem->hp_waiters[i].waiter;
	struct task_struct *donee = NULL;
	int donee_index = sem->hp_waiters[i].donee_index;
	if (donee_index != -1) {
		donee = sem->owners[donee_index];
		// NOTE: I don't know if this is necessary for the places where
		// I use kfmlp_check_hp_waiter_inhertiance, but for sanity I
		// remove the inheritance and recheck whether the waiter at
		// slot i is actually higher priority than the owner it's
		// supposed to donate to. This at least shouldn't break any of
		// the logic.
		if (tsk_rt(donee)->inh_task) {
			clear_priority_inheritance(donee);
		}
		if (edf_higher_prio(waiter, donee)) {
			set_priority_inheritance(donee, waiter);
			return;
		}
		// At this point, the old donee is actually higher priority
		// than waiter i, so we need to find a new donee if possible.
		sem->hp_waiters[i].donee_index = -1;
		donee_index = -1;
	}

	// We weren't donating priority, so see if we need to.
	donee_index = kfmlp_find_highest_lp_owner(sem, waiter);
	// Quit now if all lock holders are already higher priority.
	if (donee_index < 0) return;
	// Finally, donate our priority.
	sem->hp_waiters[i].donee_index = donee_index;
	set_priority_inheritance(sem->owners[donee_index], waiter);
}

// Returns the index of an HP waiter slot that is unoccupied. Bugs if all are
// occupied. (Check ahead of time that sem->num_waiters is less than sem->k)
static int kfmlp_find_empty_hp_waiter_slot(struct kfmlp_semaphore *sem)
{
	int i;
	for (i = 0; i < sem->k; i++) {
		if (!sem->hp_waiters[i].waiter) return i;
	}
	printk("Likely bug! kfmlp_find_empty_hp_waiter_slot called when all "
		"slots are occupied\n");
	BUG();
	return -1;
}

// Returns the task_struct for the lowest-priority of the highest-priority
// waiters. Returns NULL if there are no waiters.
static struct task_struct* kfmlp_lowest_hp_waiter(struct kfmlp_semaphore *sem)
{
	if (sem->lowest_hp_waiter < 0) return NULL;
	return sem->hp_waiters[sem->lowest_hp_waiter].waiter;
}

// Finds the new highest-priority waiter with the lowest priority.
static void kfmlp_update_lp_hp_waiter(struct kfmlp_semaphore *sem)
{
	struct task_struct *candidate = NULL;
	int candidate_index = -1;
	int i;
	for (i = 0; i < sem->k; i++)
	{
		if (sem->hp_waiters[i].waiter == NULL) continue;
		if (candidate == NULL) {
			candidate_index = i;
			candidate = sem->hp_waiters[i].waiter;
			continue;
		}
		if (edf_higher_prio(sem->hp_waiters[i].waiter, candidate)) {
			// The current candidate is lower priority.
			continue;
		}
		candidate = sem->hp_waiters[i].waiter;
		candidate_index = i;
	}
	// The index will still correctly be -1 if there were no waiters.
	sem->lowest_hp_waiter = candidate_index;
}

// To be called whenever a new waiter (t) has been added to sem's wait queue.
// This function updates the list of highest-priority waiters (if t is a new
// HP waiter), and sets priority inheritance appropriately. Also updates
// sem->num_waiters.
static void kfmlp_new_waiter_added(struct kfmlp_semaphore *sem,
	struct task_struct *t)
{
	// Things this function does:
	//  - If t isn't a HP waiter, return.
	//  - If there were fewer than k HP waiters, just add t to the list,
	//    and donate its priority if needed.
	//  - If there were already k HP waiters, see if it's higher priority
	//    than the LP waiter. If the LP waiter was donating its priority,
	//    then donate t's priority instead. If it wasn't see if t needs to
	//    donate priority. (handled in kfmlp_check_hp_waiter_inheritance)
	int waiter_slot = -1;
	if (sem->num_waiters < sem->k) {
		// There are fewer than k waiters, so we're one of the top k
		waiter_slot = kfmlp_find_empty_hp_waiter_slot(sem);
		sem->hp_waiters[waiter_slot].waiter = t;
		sem->hp_waiters[waiter_slot].donee_index = -1;
		// See if we're lower priority than the prior lowest-priority
		// waiter, if one existed.
		if ((sem->lowest_hp_waiter < 0) ||
			edf_higher_prio(kfmlp_lowest_hp_waiter(sem), t)) {
			sem->lowest_hp_waiter = waiter_slot;
		}
		sem->num_waiters++;
		kfmlp_check_hp_waiter_inheritance(sem, waiter_slot);
		return;
	}
	if (edf_higher_prio(kfmlp_lowest_hp_waiter(sem), t)) {
		// We're lower priority than the lowest-priority of the HP
		// waiters, so we're not going to donate priority (yet, at
		// least).
		sem->num_waiters++;
		return;
	}
	// We'll replace the lowest-priority HP waiter, and donate our priority
	// to its donee instead.
	waiter_slot = sem->lowest_hp_waiter;
	sem->hp_waiters[waiter_slot].waiter = t;
	kfmlp_check_hp_waiter_inheritance(sem, waiter_slot);
	sem->num_waiters++;
	kfmlp_update_lp_hp_waiter(sem);
}

// If t is in the wait queue, then remove its entry. The queue's lock must be
// held already.
static void kfmlp_remove_from_wait_queue(struct kfmlp_semaphore *sem,
	struct task_struct *t)
{
	struct list_head *pos = NULL;
	wait_queue_entry_t *queue_entry = NULL;
	int found = 0;
	list_for_each(pos, &(sem->wait.head)) {
		queue_entry = (wait_queue_entry_t *) list_entry(pos,
			wait_queue_entry_t, entry);
		if (queue_entry->private == (void *) t) {
			found = 1;
			break;
		}
	}
	if (found) {
		__remove_wait_queue(&(sem->wait), queue_entry);
		TRACE("Removed task %d from kfmlp wait queue\n", (int) t->pid);
	} else {
		TRACE("Couldn't remove task %d from wait queue: not found\n",
			(int) t->pid);
	}
}

// Returns t's slot in the list of HP waiters, or -1 if it isn't an HP waiter.
// waiter in exclude_slot. Set exclude_slot to -1 to check every HP waiter.
static int kfmlp_get_hp_waiter_slot(struct kfmlp_semaphore *sem,
	struct task_struct *t)
{
	int i;
	for (i = 0; i < sem->k; i++) {
		if (sem->hp_waiters[i].waiter == t) return i;
	}
	return -1;
}

// Searches through the wait queue to find a highest-priority waiter to fill an
// empty slot. Returns NULL if there are no waiters that aren't already in HP
// waiter slots. Simply returns the highest priority waiter that isn't in an HP
// waiter slot already.
static struct task_struct* kfmlp_find_new_hp_waiter(
	struct kfmlp_semaphore *sem)
{
	struct list_head *pos;
	wait_queue_entry_t *queue_entry = NULL;
	struct task_struct *candidate = NULL;
	struct task_struct *t = NULL;
	list_for_each(pos, &(sem->wait.head)) {
		queue_entry = (wait_queue_entry_t *) list_entry(pos,
			wait_queue_entry_t, entry);
		t = (struct task_struct *) queue_entry->private;
		if (kfmlp_get_hp_waiter_slot(sem, t) >= 0) {
			// Ignore waiters that are already HP.
			continue;
		}
		if (!candidate || edf_higher_prio(t, candidate)) {
			candidate = t;
		}
	}
	return candidate;
}

// Replaces the highest-priority waiter with a new one from the wait queue.
// This may occur when the waiter currently in the slot has either been granted
// a lock slot (in which case it must have already been put in the correct
// owners slot), or it may have been interrupted.
static void kfmlp_replace_hp_waiter(struct kfmlp_semaphore *sem, int slot)
{
	struct task_struct *new_hp_waiter = NULL;
	int old_donee_index = sem->hp_waiters[slot].donee_index;
	if (!sem->hp_waiters[slot].waiter) {
		TRACE("Error! Got invalid slot for replace_hp_waiter.\n");
		return;
	}
	sem->hp_waiters[slot].waiter = NULL;
	sem->hp_waiters[slot].donee_index = -1;
	if (old_donee_index >= 0) {
		clear_priority_inheritance(sem->owners[old_donee_index]);
	}
	new_hp_waiter = kfmlp_find_new_hp_waiter(sem);
	if (new_hp_waiter) {
		sem->hp_waiters[slot].waiter = new_hp_waiter;
		kfmlp_check_hp_waiter_inheritance(sem, slot);
	}

	// We either removed or replaced a HP waiter with something that is
	// lower-priority, so we may need to change the current lowest HP
	// waiter. (We can skip this if we just replaced the lowest priority
	// with something even lower.)
	if (!new_hp_waiter || (slot != sem->lowest_hp_waiter)) {
		kfmlp_update_lp_hp_waiter(sem);
	}
}

// If t was interrupted without acquiring the lock, this function will clean it
// up; removing it from the wait queue and from the list of HP waiters if it
// was one of them.
static void kfmlp_waiter_interrupted(struct kfmlp_semaphore *sem,
	struct task_struct *t)
{
	int hp_waiter_slot;
	kfmlp_remove_from_wait_queue(sem, t);
	sem->num_waiters--;
	hp_waiter_slot = kfmlp_get_hp_waiter_slot(sem, t);
	if (hp_waiter_slot < 0) return;
	kfmlp_replace_hp_waiter(sem, hp_waiter_slot);
}

static int gsnedf_kfmlp_lock(struct litmus_lock *l)
{
	struct task_struct *t = current;
	struct kfmlp_semaphore *sem = kfmlp_from_lock(l);
	wait_queue_entry_t wait;
	unsigned long flags = 0;
	int i = 0;
	if (!is_realtime(t)) return -EPERM;
	spin_lock_irqsave(&(sem->wait.lock), flags);

	// The FMLP doesn't support nested locking
	if (tsk_rt(t)->num_locks_held > 0) {
		TRACE("Preventing nested k-FMLP acquisition.\n");
		spin_unlock_irqrestore(&(sem->wait.lock), flags);
		return -EBUSY;
	}
	// Initialize this value to something indicating that we're not a lock
	// holder.
	tsk_rt(t)->ctrl_page->k_exclusion_slot = sem->k + 1;

	i = kfmlp_get_free_slot_index(sem);
	if (i >= 0) {
		// We were able to acquire a slot right away.
		sem->owners[i] = t;
		tsk_rt(t)->num_locks_held++;
		tsk_rt(t)->ctrl_page->k_exclusion_slot = i;
		spin_unlock_irqrestore(&(sem->wait.lock), flags);
		return 0;
	}

	// There wasn't a free slot---we must suspend and wait.
	init_waitqueue_entry(&wait, t);
	// The original FMLP used uninterruptible. Is there anything
	// fundamentally broken about interruptible here? I'll give it a try.
	set_current_state(TASK_INTERRUPTIBLE);
	// Notes to self:
	//  - We use _exclusive to set the exclusive flag; we want to wake up
	//    one at a time.
	//  - We can call __add_wait_queue_entry_tail because we already hold
	//    the queue's spinlock.
	__add_wait_queue_entry_tail_exclusive(&sem->wait, &wait);

	// Handles all the priority inheritance junk.
	kfmlp_new_waiter_added(sem, t);

	// Actually suspend and wait.
	TS_LOCK_SUSPEND;
	spin_unlock_irqrestore(&sem->wait.lock, flags);
	schedule();
	TS_LOCK_RESUME;

	// NOTE: I don't know if being interrupted breaks any assumptions about
	// priority, but I don't care that much because I expect this to never
	// actually occur during experiments. Interruptible sleep is just
	// *very* nice to have to avoid locking up the whole system.
	if (!verify_kfmlp_ownership(sem)) {
		// Ugh, interrupted; we didn't get the lock.
		spin_lock_irqsave(&(sem->wait.lock), flags);
		// Check for the race condition where we may have been given
		// the lock between being interrupted and taking the spinlock.
		if (verify_kfmlp_ownership(sem)) {
			// We got the lock after all.
			tsk_rt(t)->num_locks_held++;
			spin_unlock_irqrestore(&(sem->wait.lock), flags);
			return 0;
		}
		// Remove ourselves from the wait queue and the list of HP
		// waiters if necessary.
		kfmlp_waiter_interrupted(sem, t);
		return -EINTR;
	}

	// We got the lock!
	tsk_rt(t)->num_locks_held++;
	return 0;
}

// This rechecks all highest-priority waiters that aren't currently donating
// priority, and makes them donate priority if possible.
static void kfmlp_recheck_priority_inheritance(struct kfmlp_semaphore *sem)
{
	int i = 0;
	for (i = 0; i < sem->k; i++) {
		// TODO: Change this function after making hp_waiters ordered.
		if (!sem->hp_waiters[i].waiter) continue;
		// TODO: Should we reassign this waiter to a different donee?
		if (sem->hp_waiters[i].donee_index != -1) continue;
		kfmlp_check_hp_waiter_inheritance(sem, i);
	}
}

static int gsnedf_kfmlp_unlock(struct litmus_lock *l)
{
	struct task_struct *t = current;
	struct task_struct *next = NULL;
	struct kfmlp_semaphore *sem = kfmlp_from_lock(l);
	unsigned long flags = 0;
	int owner_slot = -1;
	int hp_waiter_slot = -1;
	int i = 0;
	spin_lock_irqsave(&(sem->wait.lock), flags);
	owner_slot = kfmlp_get_owner_slot(sem);
	if (owner_slot < 0) {
		TRACE("Got kfmlp unlock from non-owner!\n");
		spin_unlock_irqrestore(&(sem->wait.lock), flags);
		return -EINVAL;
	}
	tsk_rt(t)->num_locks_held--;
	if (tsk_rt(t)->inh_task) {
		// In addition to clearing priority inheritance, make sure the
		// donor is no longer marked as donating.
		clear_priority_inheritance(t);
		for (i = 0; i < sem->k; i++) {
			if (sem->hp_waiters[i].donee_index == owner_slot) {
				sem->hp_waiters[i].donee_index = -1;
			}
		}
	}
	next = __waitqueue_remove_first(&(sem->wait));
	sem->num_waiters--;
	if (!next) {
		// There are no more waiters, so we can't have been inheriting
		// priority. Simply clear our slot and return.
		sem->owners[owner_slot] = NULL;
		spin_unlock_irqrestore(&(sem->wait.lock), flags);
		return 0;
	}
	sem->owners[owner_slot] = next;
	tsk_rt(next)->ctrl_page->k_exclusion_slot = owner_slot;

	// See if the next task was a HP waiter. If so, we need to find a
	// different HP waiter.
	hp_waiter_slot = kfmlp_get_hp_waiter_slot(sem, next);
	if (hp_waiter_slot >= 0) {
		kfmlp_replace_hp_waiter(sem, hp_waiter_slot);
	}
	// Even if we didn't replace a HP waiter, we still may need to change
	// priority donation due to a waiter previously donating to the task
	// that issued this unlock call. To keep logic simpler, I'll just
	// recheck all HP waiters to see if they can donate to a lock holder.
	kfmlp_recheck_priority_inheritance(sem);

	// Allow the next owner to start running.
	wake_up_process(next);
	spin_unlock_irqrestore(&(sem->wait.lock), flags);
	return 0;
}

static int gsnedf_kfmlp_close(struct litmus_lock *l)
{
	struct kfmlp_semaphore *sem = kfmlp_from_lock(l);
	int slot = 0;
	unsigned long flags = 0;
	spin_lock_irqsave(&(sem->wait.lock), flags);
	slot = kfmlp_get_owner_slot(sem);
	spin_unlock_irqrestore(&(sem->wait.lock), flags);
	if (slot < 0) {
		// We weren't holding the lock.
		return 0;
	}
	return gsnedf_kfmlp_unlock(l);
}

static struct litmus_lock_ops gsnedf_kfmlp_lock_ops = {
	.close  = gsnedf_kfmlp_close,
	.lock   = gsnedf_kfmlp_lock,
	.unlock = gsnedf_kfmlp_unlock,
	.deallocate = gsnedf_kfmlp_free,
};

// Requires a pointer to an int in userspace, indicating the "k" value.
static struct litmus_lock* gsnedf_new_kfmlp(void* __user config)
{
	struct kfmlp_semaphore *sem = NULL;
	int k = -1;
	if (get_user(k, (int *) config) != 0) {
		TRACE("Failed getting k-value from user.\n");
		return NULL;
	}
	if (k <= 0) {
		TRACE("Got a non-positive k-value from user.\n");
		return NULL;
	}
	if (k > MAX_KFMLP_K) {
		TRACE("Got a value of k (%d) above the limit of %d.\n", k,
			MAX_KFMLP_K);
		return NULL;
	}
	TRACE("Allocating new k-exclusion lock with k = %d\n", k);
	sem = kmalloc(sizeof(*sem), GFP_KERNEL);
	if (!sem) return NULL;
	memset(sem, 0, sizeof(*sem));
	sem->k = k;
	sem->lowest_hp_waiter = -1;
	init_waitqueue_head(&sem->wait);
	sem->litmus_lock.ops = &gsnedf_kfmlp_lock_ops;
	return &(sem->litmus_lock);
}

/* **** lock constructor **** */


static long gsnedf_allocate_lock(struct litmus_lock **lock, int type,
				 void* __user config)
{
	/* GSN-EDF currently only supports the FMLP for global resources. */
	switch (type) {

	case FMLP_SEM:
		/* Flexible Multiprocessor Locking Protocol */
		*lock = gsnedf_new_fmlp();
		break;
	case K_FMLP_SEM:
		/* Nathan's k-exclusion FMLP */
		*lock = gsnedf_new_kfmlp(config);
		break;
	default:
		return -ENXIO;
	};

	if (*lock) return 0;
	return -ENOMEM;
}

#endif

static struct domain_proc_info gsnedf_domain_proc_info;
static long gsnedf_get_domain_proc_info(struct domain_proc_info **ret)
{
	*ret = &gsnedf_domain_proc_info;
	return 0;
}

static void gsnedf_setup_domain_proc(void)
{
	int i, cpu;
	int release_master =
#ifdef CONFIG_RELEASE_MASTER
			atomic_read(&release_master_cpu);
#else
		NO_CPU;
#endif
	int num_rt_cpus = num_online_cpus() - (release_master != NO_CPU);
	struct cd_mapping *map;

	memset(&gsnedf_domain_proc_info, 0, sizeof(gsnedf_domain_proc_info));
	init_domain_proc_info(&gsnedf_domain_proc_info, num_rt_cpus, 1);
	gsnedf_domain_proc_info.num_cpus = num_rt_cpus;
	gsnedf_domain_proc_info.num_domains = 1;

	gsnedf_domain_proc_info.domain_to_cpus[0].id = 0;
	for (cpu = 0, i = 0; cpu < num_online_cpus(); ++cpu) {
		if (cpu == release_master)
			continue;
		map = &gsnedf_domain_proc_info.cpu_to_domains[i];
		map->id = cpu;
		cpumask_set_cpu(0, map->mask);
		++i;

		/* add cpu to the domain */
		cpumask_set_cpu(cpu,
			gsnedf_domain_proc_info.domain_to_cpus[0].mask);
	}
}

static long gsnedf_activate_plugin(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&gsnedf_cpu_heap);
#ifdef CONFIG_RELEASE_MASTER
	gsnedf.release_master = atomic_read(&release_master_cpu);
#endif

	for_each_online_cpu(cpu) {
		entry = &per_cpu(gsnedf_cpu_entries, cpu);
		bheap_node_init(&entry->hn, entry);
		entry->linked    = NULL;
		entry->scheduled = NULL;
#ifdef CONFIG_RELEASE_MASTER
		if (cpu != gsnedf.release_master) {
#endif
			TRACE("GSN-EDF: Initializing CPU #%d.\n", cpu);
			update_cpu_position(entry);
#ifdef CONFIG_RELEASE_MASTER
		} else {
			TRACE("GSN-EDF: CPU %d is release master.\n", cpu);
		}
#endif
	}

	gsnedf_setup_domain_proc();

	return 0;
}

static long gsnedf_deactivate_plugin(void)
{
	destroy_domain_proc_info(&gsnedf_domain_proc_info);
	return 0;
}

/*	Plugin object	*/
static struct sched_plugin gsn_edf_plugin __cacheline_aligned_in_smp = {
	.plugin_name		= "GSN-EDF",
	.finish_switch		= gsnedf_finish_switch,
	.task_new		= gsnedf_task_new,
	.complete_job		= complete_job,
	.task_exit		= gsnedf_task_exit,
	.schedule		= gsnedf_schedule,
	.task_wake_up		= gsnedf_task_wake_up,
	.task_block		= gsnedf_task_block,
	.admit_task		= gsnedf_admit_task,
	.activate_plugin	= gsnedf_activate_plugin,
	.deactivate_plugin	= gsnedf_deactivate_plugin,
	.get_domain_proc_info	= gsnedf_get_domain_proc_info,
#ifdef CONFIG_LITMUS_LOCKING
	.allocate_lock		= gsnedf_allocate_lock,
#endif
};


static int __init init_gsn_edf(void)
{
	int cpu;
	cpu_entry_t *entry;

	bheap_init(&gsnedf_cpu_heap);
	/* initialize CPU state */
	for (cpu = 0; cpu < NR_CPUS; cpu++)  {
		entry = &per_cpu(gsnedf_cpu_entries, cpu);
		gsnedf_cpus[cpu] = entry;
		entry->cpu 	 = cpu;
		entry->hn        = &gsnedf_heap_node[cpu];
		bheap_node_init(&entry->hn, entry);
	}
	edf_domain_init(&gsnedf, NULL, gsnedf_release_jobs);
	return register_sched_plugin(&gsn_edf_plugin);
}


module_init(init_gsn_edf);
