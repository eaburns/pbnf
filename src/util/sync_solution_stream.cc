/**
 * \file sync_solution_stream.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */

#include <iostream>

using namespace std;

#include <stdlib.h>

extern "C" {
#include "../lockfree/include/atomic.h"
}

#include "../state.h"
#include "sync_solution_stream.h"
#include "solution_stream.h"
#include "timer.h"

SyncSolutionStream::SyncSolutionStream(Timer *t, double g)
	: SolutionStream(t, g), lst(NULL)
{
}

fp_type SyncSolutionStream::see_solution(vector<State *> *path,
					 unsigned int gen,
					 unsigned int exp)
{
	double time = timer->get_lap_time();
	fp_type cost = path->at(0)->get_g();
	int success = 0;

	Solution *s = lst;

	if (s && cost * granularity >= s->path->at(0)->get_g())
		return lst->path->at(0)->get_g();

	Solution *t = new Solution(path, gen, exp, time);
	while (!s || cost * granularity < s->path->at(0)->get_g()) {
		t->next = s;

		success = compare_and_swap(&lst, (intptr_t) s, (intptr_t) t);
		if (success)
			break;

		s = lst;
	}

	if (!success)
		delete t;

	return lst->path->at(0)->get_g();
}

vector<State *> *SyncSolutionStream::get_best_path(void)
{
	Solution *s = lst;

	if (s == NULL)
		return NULL;

	return s->path;
}

void SyncSolutionStream::output(ostream &o)
{
	SolutionStream::do_output(o, lst);
}

