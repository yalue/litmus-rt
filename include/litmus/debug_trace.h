#ifndef LITMUS_DEBUG_TRACE_H
#define LITMUS_DEBUG_TRACE_H
#include <litmus/debug_trace_common.h>

#define TRACE(fmt, args...)						\
	sched_trace_log_message(TRACE_PREFIX fmt,			\
				TRACE_ARGS,  ## args)

#define TRACE_TASK(t, fmt, args...)			\
	TRACE("(%s/%d:%d) " fmt,			 \
	      t ? (t)->comm : "null",			 \
	      t ? (t)->pid : 0,				 \
	      t ? (t)->rt_param.job_params.job_no : 0,	 \
	      ##args)

#define TRACE_CUR(fmt, args...) \
	TRACE_TASK(current, fmt, ## args)

#define TRACE_WARN_ON(cond) \
	if (unlikely(cond)) \
		TRACE("WARNING: '%s' [%s@%s:%d]\n", \
			#cond, __FUNCTION__, __FILE__, __LINE__)

#endif
