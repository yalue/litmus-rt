/* This file is included from kernel/sched.c */

#include "sched.h"

#include <litmus/trace.h>
#include <litmus/sched_trace.h>

#include <litmus/debug_trace.h>
#include <litmus/litmus.h>
#include <litmus/budget.h>
#include <litmus/sched_plugin.h>
#include <litmus/preempt.h>
#include <litmus/np.h>

static void update_time_litmus(struct rq *rq, struct task_struct *p)
{
	u64 delta = rq->clock - p->se.exec_start;
	if (unlikely((s64)delta < 0))
		delta = 0;
	/* per job counter */
	p->rt_param.job_params.exec_time += delta;
	/* task counter */
	p->se.sum_exec_runtime += delta;
	if (delta) {
		TRACE_TASK(p, "charged %llu exec time (total:%llu, rem:%llu)\n",
			delta, p->rt_param.job_params.exec_time, budget_remaining(p));
	}
	/* sched_clock() */
	p->se.exec_start = rq->clock;
	cpuacct_charge(p, delta);
}

extern void double_rq_lock(struct rq *rq1, struct rq *rq2);
extern void double_rq_unlock(struct rq *rq1, struct rq *rq2);

static struct task_struct *
litmus_schedule(struct rq *rq, struct task_struct *prev)
{
	struct task_struct *next;

#ifdef CONFIG_SMP
	struct rq* other_rq;
	long was_running;
	int from_where;
	lt_t _maybe_deadlock = 0;
#endif

	/* let the plugin schedule */
	next = litmus->schedule(prev);

	sched_state_plugin_check();

#ifdef CONFIG_SMP
	/* check if a global plugin pulled a task from a different RQ */
	if (next && task_rq(next) != rq) {
		/* we need to migrate the task */
		other_rq = task_rq(next);
		from_where = other_rq->cpu;
		TRACE_TASK(next, "migrate from %d\n", from_where);

		/* while we drop the lock, the prev task could change its
		 * state
		 */
		BUG_ON(prev != current);
		was_running = is_current_running();

		/* Don't race with a concurrent switch.  This could deadlock in
		 * the case of cross or circular migrations.  It's the job of
		 * the plugin to make sure that doesn't happen.
		 */
		TRACE_TASK(next, "stack_in_use=%d\n",
			   next->rt_param.stack_in_use);
		if (next->rt_param.stack_in_use != NO_CPU) {
			TRACE_TASK(next, "waiting to deschedule\n");
			_maybe_deadlock = litmus_clock();
		}

		raw_spin_rq_unlock(rq);

		while (next->rt_param.stack_in_use != NO_CPU) {
			cpu_relax();
			mb();
			if (next->rt_param.stack_in_use == NO_CPU)
				TRACE_TASK(next,"descheduled. Proceeding.\n");

			if (!litmus->should_wait_for_stack(next)) {
				/* plugin aborted the wait */
				TRACE_TASK(next,
				           "plugin gave up waiting for stack\n");
				next = NULL;
				/* Make sure plugin is given a chance to
				 * reconsider. */
				litmus_reschedule_local();
				/* give up */
				raw_spin_rq_lock(rq);
				goto out;
			}

			if (from_where != task_rq(next)->cpu) {
				/* The plugin should not give us something
				 * that other cores are trying to pull, too */
				TRACE_TASK(next, "next invalid: task keeps "
				                 "shifting around!? "
				                 "(%d->%d)\n",
				                 from_where,
				                 task_rq(next)->cpu);

				/* bail out */
				raw_spin_rq_lock(rq);
				litmus->next_became_invalid(next);
				litmus_reschedule_local();
				next = NULL;
				goto out;
			}

			if (lt_before(_maybe_deadlock + 1000000000L,
				      litmus_clock())) {
				/* We've been spinning for 1s.
				 * Something can't be right!
				 * Let's abandon the task and bail out; at least
				 * we will have debug info instead of a hard
				 * deadlock.
				 */
#ifdef CONFIG_BUG_ON_MIGRATION_DEADLOCK
				BUG();
#else
				TRACE_TASK(next,"stack too long in use. "
					   "Deadlock?\n");
				next = NULL;

				/* bail out */
				raw_spin_rq_lock(rq);
				goto out;
#endif
			}
		}
#ifdef  __ARCH_WANT_UNLOCKED_CTXSW
		if (next->on_cpu)
			TRACE_TASK(next, "waiting for !oncpu");
		while (next->on_cpu) {
			cpu_relax();
			mb();
		}
#endif
		double_rq_lock(rq, other_rq);
		if (other_rq == task_rq(next) &&
		    next->rt_param.stack_in_use == NO_CPU) {
			/* ok, we can grab it */
			set_task_cpu(next, rq->cpu);
			/* release the other CPU's runqueue, but keep ours */
			raw_spin_rq_unlock(other_rq);
		} else {
			/* Either it moved or the stack was claimed; both is
			 * bad and forces us to abort the migration. */
			TRACE_TASK(next, "next invalid: no longer available\n");
			raw_spin_rq_unlock(other_rq);
			litmus->next_became_invalid(next);
			next = NULL;
			goto out;
		}

		if (!litmus->post_migration_validate(next)) {
			TRACE_TASK(next, "plugin deems task now invalid\n");
			litmus_reschedule_local();
			next = NULL;
		}
	}
#endif

	/* check if the task became invalid while we dropped the lock */
	if (next && (!is_realtime(next) || !tsk_rt(next)->present)) {
		TRACE_TASK(next,
			"BAD: next (no longer?) valid\n");
		litmus->next_became_invalid(next);
		litmus_reschedule_local();
		next = NULL;
	}

	if (next) {
#ifdef CONFIG_SMP
		next->rt_param.stack_in_use = rq->cpu;
#else
		next->rt_param.stack_in_use = 0;
#endif
		update_rq_clock(rq);
		next->se.exec_start = rq->clock;
	}

out:
	update_enforcement_timer(next);
	return next;
}

static void enqueue_task_litmus(struct rq *rq, struct task_struct *p,
				int flags)
{
	tsk_rt(p)->present = 1;
	if (flags & ENQUEUE_WAKEUP) {
		sched_trace_task_resume(p);
		/* LITMUS^RT plugins need to update the state
		 * _before_ making it available in global structures.
		 * Linux gets away with being lazy about the task state
		 * update. We can't do that, hence we update the task
		 * state already here.
		 *
		 * WARNING: this needs to be re-evaluated when porting
		 *          to newer kernel versions.
		 */
		WRITE_ONCE(current->__state, TASK_RUNNING);
		litmus->task_wake_up(p);

		rq->litmus.nr_running++;
	} else {
		TRACE_TASK(p, "ignoring an enqueue, not a wake up.\n");
		p->se.exec_start = rq->clock;
	}
}

static void dequeue_task_litmus(struct rq *rq, struct task_struct *p,
				int flags)
{
	if (flags & DEQUEUE_SLEEP) {
#ifdef CONFIG_SCHED_TASK_TRACE
		tsk_rt(p)->job_params.last_suspension = litmus_clock();
#endif
		litmus->task_block(p);
		tsk_rt(p)->present = 0;
		sched_trace_task_block(p);

		rq->litmus.nr_running--;
	} else
		TRACE_TASK(p, "ignoring a dequeue, not going to sleep.\n");
}

static void yield_task_litmus(struct rq *rq)
{
	TS_SYSCALL_IN_START;
	TS_SYSCALL_IN_END;

	BUG_ON(rq->curr != current);
	/* sched_yield() is called to trigger delayed preemptions.
	 * Thus, mark the current task as needing to be rescheduled.
	 * This will cause the scheduler plugin to be invoked, which can
	 * then determine if a preemption is still required.
	 */
	clear_exit_np(current);
	litmus_reschedule_local();

	TS_SYSCALL_OUT_START;
}

/* Plugins are responsible for this.
 */
static void check_preempt_curr_litmus(struct rq *rq, struct task_struct *p, int flags)
{
}

static void put_prev_task_litmus(struct rq *rq, struct task_struct *p)
{
}

/* pick_next_task_litmus() - litmus_schedule() function
 *
 * prev and rf are deprecated by our caller and unused
 * returns the next task to be scheduled
 */
static struct task_struct *pick_next_task_litmus(struct rq *rq)
{
	struct task_struct *next;

	if (is_realtime(rq->curr))
		update_time_litmus(rq, rq->curr);

	/* litmus_schedule() should be wrapped by the rq_upin_lock() and
	 * rq_repin_lock() annotations. Unfortunately, these annotations can
	 * not presently be added meaningfully as we are not passed rf->cookie.
	 */
	TS_PLUGIN_SCHED_START;
	next = litmus_schedule(rq, rq->curr);
	TS_PLUGIN_SCHED_END;

	return next;
}

static void task_tick_litmus(struct rq *rq, struct task_struct *p, int queued)
{
	if (is_realtime(p) && !queued) {
		update_time_litmus(rq, p);
		/* budget check for QUANTUM_ENFORCEMENT tasks */
		if (budget_enforced(p) && budget_exhausted(p)) {
			litmus_reschedule_local();
		}
	}
}

static void switched_to_litmus(struct rq *rq, struct task_struct *p)
{
}

static void prio_changed_litmus(struct rq *rq, struct task_struct *p,
				int oldprio)
{
}

unsigned int get_rr_interval_litmus(struct rq *rq, struct task_struct *p)
{
	/* return infinity */
	return 0;
}

/* This is called when a task became a real-time task, either due to a SCHED_*
 * class transition or due to PI mutex inheritance. We don't handle Linux PI
 * mutex inheritance yet (and probably never will). Use LITMUS provided
 * synchronization primitives instead.
 */
static void set_next_task_litmus(struct rq *rq, struct task_struct *p, bool first)
{
	p->se.exec_start = rq->clock;
}


#ifdef CONFIG_SMP
static int
balance_litmus(struct rq *rq, struct task_struct *prev, struct rq_flags *rf)
{
	return 1;
}

/* execve tries to rebalance task in this scheduling domain.
 * We don't care about the scheduling domain; can gets called from
 * exec, fork, wakeup.
 */
static int
select_task_rq_litmus(struct task_struct *p, int cpu, int flags)
{
	/* preemption is already disabled.
	 * We don't want to change cpu here
	 */
	return task_cpu(p);
}
#endif

static void update_curr_litmus(struct rq *rq)
{
	struct task_struct *p = rq->curr;

	if (!is_realtime(p))
		return;

	update_time_litmus(rq, p);
}

DEFINE_SCHED_CLASS(litmus) = {
	.enqueue_task		= enqueue_task_litmus,
	.dequeue_task		= dequeue_task_litmus,
	.yield_task		= yield_task_litmus,

	.check_preempt_curr	= check_preempt_curr_litmus,

	.pick_next_task		= pick_next_task_litmus,
	.put_prev_task		= put_prev_task_litmus,

#ifdef CONFIG_SMP
	.balance		= balance_litmus,
	.select_task_rq		= select_task_rq_litmus,
#endif

	.set_next_task		= set_next_task_litmus,
	.task_tick		= task_tick_litmus,

	.get_rr_interval	= get_rr_interval_litmus,

	.prio_changed		= prio_changed_litmus,
	.switched_to		= switched_to_litmus,

	.update_curr		= update_curr_litmus,
};
