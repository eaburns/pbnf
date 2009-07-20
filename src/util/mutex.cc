/**
 * \file mutex.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-07-20
 */

#include <errno.h>
#include <pthread.h>

#include "timer.h"
#include "mutex.h"

Mutex::Mutex(void)
{
	pthread_mutex_init(&mutex, NULL);
}

void Mutex::lock(void)
{
	timer.start();
	pthread_mutex_lock(&mutex);
	timer.stop();

	total_time += timer.get_wall_time();
}

void Mutex::unlock(void)
{
	pthread_mutex_unlock(&mutex);
}

bool Mutex::try_lock(void)
{
	return pthread_mutex_trylock(&mutex) != EBUSY;
}

double Mutex::get_time_spent_waiting(void)
{
	return total_time;
}
