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

#include <ostream>

using namespace std;

#include "timer.h"
#include "mutex.h"

Mutex::Mutex(void)
{
	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
	lock_acquisition_time = 0.0;
	cond_wait_time = 0.0;
}

void Mutex::lock(void)
{
	Timer t;

	t.start();
	pthread_mutex_lock(&mutex);
	t.stop();

	lock_acquisition_time += t.get_wall_time();
}

void Mutex::unlock(void)
{
	pthread_mutex_unlock(&mutex);
}

bool Mutex::try_lock(void)
{
	return pthread_mutex_trylock(&mutex) != EBUSY;
}

void Mutex::cond_wait(void)
{
	Timer t;

	t.start();
	pthread_cond_wait(&cond, &mutex);
	t.stop();

	cond_wait_time += t.get_wall_time();
}

void Mutex::cond_signal(void)
{
	pthread_cond_signal(&cond);
}

void Mutex::cond_broadcast(void)
{
	pthread_cond_broadcast(&cond);
}

double Mutex::get_lock_acquisition_time(void)
{
	return lock_acquisition_time;
}

double Mutex::get_cond_wait_time(void)
{
	return cond_wait_time;
}

void Mutex::print_stats(ostream &o)
{
	o << "time-acquiring-locks: " << lock_acquisition_time << endl;
	o << "time-waiting: " << cond_wait_time << endl;
}
