/**
 * \file serial_solution_stream.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-20
 */
#include <iostream>

using namespace std;

#include "../state.h"
#include "solution_stream.h"
#include "serial_solution_stream.h"
#include "timer.h"

SerialSolutionStream::SerialSolutionStream(Timer *t, double g)
	: SolutionStream(t, g), best(NULL), lst(NULL)
{
}

void SerialSolutionStream::see_solution(vector<State *> *path,
					 unsigned int gen,
					 unsigned int exp)
{
	double time = timer->get_lap_time();

	if (!better(path, best))
		return;

	Solution *t = new Solution(path, gen, exp, time);
	best = t;

	if (within_gran(path, lst)) {
		t->next = lst;
		lst = t;
	}
}

vector<State *> *SerialSolutionStream::get_best_path(void)
{
	if (!best)
		return NULL;

	return best->path;
}

/**
 * Not meant to be called atomically.
 */
void SerialSolutionStream::output(ostream &o)
{
	if (best->next == NULL && lst != best)
		best->next = lst;

	SolutionStream::do_output(o, best);
}


