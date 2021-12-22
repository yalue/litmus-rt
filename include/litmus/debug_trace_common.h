#ifdef CONFIG_SCHED_DEBUG_TRACE
void sched_trace_log_message(const char* fmt, ...);
void dump_trace_buffer(int max);
#else

#define sched_trace_log_message(fmt, ...)

#endif

extern atomic_t __log_seq_no;

#ifdef CONFIG_SCHED_DEBUG_TRACE_CALLER
#define TRACE_PREFIX "%d P%d [%s@%s:%d]: "
#define TRACE_ARGS  atomic_add_return(1, &__log_seq_no),	\
		raw_smp_processor_id(),				\
		__FUNCTION__, __FILE__, __LINE__
#else
#define TRACE_PREFIX "%d P%d: "
#define TRACE_ARGS  atomic_add_return(1, &__log_seq_no), \
		raw_smp_processor_id()
#endif
