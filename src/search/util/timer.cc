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

void Timer::start(void)
{
	struct timeval t;

	gettimeofday(&t, NULL);
	start_time = t.tv_usec;
	start_time /= 1000000;
	start_time += t.tv_sec;
}

double Timer::stop(void)
{
	struct timeval t;
	double stop;

	gettimeofday(&t, NULL);
	stop = t.tv_usec;
	stop /= 1000000;
	stop += t.tv_sec;

	return stop - start_time;
}
