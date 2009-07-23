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

#include <iostream>

using namespace std;

#include "mutex.h"

ThreadSpecific<double> Mutex::lock_acquisition_times(0.0);
ThreadSpecific<double> Mutex::cond_wait_times(0.0);

Mutex::Mutex(void)
{
	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
}

void Mutex::lock(void)
{
	Timer t;

	t.start();
	pthread_mutex_lock(&mutex);
	t.stop();

	double time = lock_acquisition_times.get_value();
	lock_acquisition_times.set_value(time + t.get_wall_time());
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

	double time = cond_wait_times.get_value();
	cond_wait_times.set_value(time + t.get_wall_time());
}

void Mutex::cond_signal(void)
{
	pthread_cond_signal(&cond);
}

void Mutex::cond_broadcast(void)
{
	pthread_cond_broadcast(&cond);
}

double Mutex::get_total_lock_acquisition_time(void)
{
	double total_time;
	vector<double> times;
	vector<double>::iterator iter;

	times = lock_acquisition_times.get_all_entries();
	total_time = 0.0;
	for (iter = times.begin(); iter != times.end(); iter++)
		total_time += (*iter);

	return total_time;
}

double Mutex::get_total_cond_wait_time(void)
{
	double total_time;
	vector<double> times;
	vector<double>::iterator iter;

	times = cond_wait_times.get_all_entries();
	total_time = 0.0;
	for (iter = times.begin(); iter != times.end(); iter++)
		total_time += (*iter);

	return total_time;

}

void Mutex::print_stats(ostream &o)
{
	o << "total-time-acquiring-locks: "
	  << get_total_lock_acquisition_time() << endl;
	o << "total-time-waiting: "
	  << get_total_cond_wait_time() << endl;
}
