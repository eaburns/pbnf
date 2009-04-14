/**
 * \file sync_solution_stream.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */

#include <pthread.h>
#include <stdlib.h>

#include "../state.h"
#include "sync_solution_stream.h"
#include "solution_stream.h"
#include "timer.h"

SyncSolutionStream::SyncSolutionStream(Timer *t, double g)
	: SolutionStream(t, g)
{
	pthread_mutex_init(&mutex, NULL);
}

fp_type SyncSolutionStream::see_solution(vector<State *> *path,
					 unsigned int gen,
					 unsigned int exp)
{
	fp_type ret;

	pthread_mutex_lock(&mutex);
	ret = SyncSolutionStream::see_solution(path, gen, exp);
	pthread_mutex_unlock(&mutex);

	return ret;
}
