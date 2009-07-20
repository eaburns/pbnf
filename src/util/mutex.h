/**
 * \file mutex.h
 *
 *
 *
 * \author eaburns
 * \date 2009-07-20
 */

#if !defined(_MUTEX_H_)
#define _MUTEX_H_

#include <pthread.h>

#include "timer.h"

class Mutex {
public:
	Mutex(void);

	/* Lock the mutex */
	void lock(void);

	/* Unlock the mutex */
	void unlock(void);

	/* Try the lock on the mutex, returns true if the lock is
	 * acquired and false if not. */
	bool try_lock(void);

	/* Get the total time (in seconds) that threads have spent
	 * waiting on this mutex. */
	double get_time_spent_waiting(void);
private:
	Timer timer;
	double total_time;
	pthread_mutex_t mutex;
};

#endif	/* _MUTEX_H_ */
