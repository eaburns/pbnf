/**
 * \file sync_solution_stream.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */

#include <pthread.t>
#include <stdlib.h>

#include "solution_stream.h"

SyncSolutionStream::SyncSolutionStream(Timer *t, double g)
{
	super(t, g);
	pthread_mutex_init(&mutex, NULL);
}

fp_type SolutionStream::see_solution(vector<State *> *path,
				     unsigned int gen,
				     unsigned int exp)
{
	fp_type ret;

	pthread_mutex_lock(&mutex);
	ret = super.see_solution(path, gen, exp);
	pthread_mutex_unlock(&mutex);

	return ret;
}
