/* -*- mode:linux -*- */
/**
 * \file timer.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#include <sys/time.h>
#include <time.h>

#include "timer.h"

Timer::Timer(void)
	: start_time(0),
	  elapsed(0),
	  running(false){}


void Timer::start(void)
{
	struct timeval t;

	elapsed = 0;

	gettimeofday(&t, NULL);
	start_time = t.tv_usec;
	start_time /= 1000000;
	start_time += t.tv_sec;

	running = true;
}


double Timer::compute_elapsed(void)
{
	struct timeval t;
	double stop;

	gettimeofday(&t, NULL);
	stop = t.tv_usec;
	stop /= 1000000;
	stop += t.tv_sec;

	return stop - start_time;
}


double Timer::stop(void)
{
	elapsed = compute_elapsed();
	running = false;

	return elapsed;
}

double Timer::get_elapsed(void)
{
	if (running)
		elapsed = compute_elapsed();

	return elapsed;
}
