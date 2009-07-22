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

#include <ostream>

using namespace std;

#include "timer.h"
#include "atomic_float.h"

class Mutex {
public:
	Mutex(void);

	/** Lock the mutex */
	void lock(void);

	/** Unlock the mutex */
	void unlock(void);

	/**
	 * Try the lock on the mutex, returns true if the lock is
	 * acquired and false if not.
	 */
	bool try_lock(void);

	/** Wait on the condition. */
	void cond_wait(void);

	/** Signal one threads waiting on the condition. */
	void cond_signal(void);

	/** Signal all threads waiting on the condition. */
	void cond_broadcast(void);

	/**
	 * Get the total time (in seconds) that threads have spent
	 * waiting on this mutex.
	 */
	static double get_lock_acquisition_time(void);

	/**
	 * Get the amount of time spent waiting on a condition.
	 */
	static double get_cond_wait_time(void);

	/** Print the stats to the given output stream. */
	static void print_stats(ostream &o);

private:
	/** The accumulated time spent trying to acquire a lock. */
	static AtomicFloat lock_acquisition_time;

	/** Accumulated time waiting on a condition. */
	static AtomicFloat cond_wait_time;

	/** The low-level mutex. */
	pthread_mutex_t mutex;

	/** Incase we want a condition on this mutex. */
	pthread_cond_t cond;
};

#endif	/* _MUTEX_H_ */
