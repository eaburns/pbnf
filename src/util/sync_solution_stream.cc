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
	: SolutionStream(t, g), lst(NULL), best(NULL)
{
}

void SyncSolutionStream::see_solution(vector<State *> *path,
					 unsigned int gen,
					 unsigned int exp)
{
	bool can_free = true;
	double time = timer->get_lap_time();

	Solution *b = best;
	if (!better(path, b))
		return;

	Solution *t = new Solution(path, gen, exp, time);

	while (better(path, b)) {
		if (compare_and_swap(&best, (intptr_t) b, (intptr_t) t)) {
			can_free = false;
			break;
		}
		b = best;
	}

	int success = 0;
	Solution *s = lst;
	while (within_gran(path, s)) {
		t->next = s;

		success = compare_and_swap(&lst, (intptr_t) s, (intptr_t) t);
		if (success) {
			can_free = false;
			break;
		}

		s = lst;
	}

	if (!can_free) {
		// was either set as 'best' solution or was added to
		// the list or both... hold on to it.
		Solution *q = all;
		while (!compare_and_swap(&all, (intptr_t) q, (intptr_t) t))
			q = all;
	} else {
		// wasn't added to anything and it can be freed.
		delete t;
	}
}

vector<State *> *SyncSolutionStream::get_best_path(void)
{
	Solution *b = best;

	if (!b)
		return NULL;

	return b->path;
}

/**
 * Not meant to be called atomically.
 */
void SyncSolutionStream::output(ostream &o)
{
	if (best->next == NULL)
		best->next = lst;

	SolutionStream::do_output(o, best);
}

