/* -*- mode:linux -*- */
/**
 * \file completion_counter.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-24
 */

#if !defined(_COMPLETION_COUNTER_H_)
#define _COMPLETION_COUNTER_H_

#include <pthread.h>

class CompletionCounter {
public:
        CompletionCounter(): counter(0), max(max) {};
	CompletionCounter(unsigned int max);

	void complete(void);
	void wait(void);
	void reset(void);

private:
	pthread_mutex_t mutex;
	pthread_cond_t cond;
	unsigned int counter;
	unsigned int max;
};

#endif	/* !_COMPLETION_COUNTER_H_ */
