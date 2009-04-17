/**
 * \file solution_stream.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */

#include <stdlib.h>

#include <queue>
#include <iostream>

#include "solution_stream.h"
#include "fixed_point.h"

using namespace std;

SolutionStream::SolutionStream(Timer *t, double g)
	: timer(t),
	  granularity(g * fp_one)
{
}

/*
fp_type SolutionStream::see_solution(vector<State *> *path,
				     unsigned int gen,
				     unsigned int exp)
{
	double time = timer->get_lap_time();
	fp_type cost = path->at(0)->get_g();

	if (!best_path || cost * granularity < best_cost) {
		Solution s(cost, path->size(), gen, exp, time);

		best_path = path;
		best_cost = cost;
		solutions.push(s);
	}

	return best_cost;
}

vector<State *> *SolutionStream::get_best_path(void)
{
	return best_path;
}
*/

void SolutionStream::do_output_recur(ostream &o, Solution *s)
{
	if (!s)
		return;

	do_output_recur(o, s->next);

	o << "row: "
	  << s->path->at(0)->get_g() / fp_one << " "
	  << s->path->size() << " "
	  << s->generated << " "
	  << s->expanded << " "
	  << s->time << endl;
}

void SolutionStream::do_output(ostream &o, Solution *s)
{

	if (!s)
		return;

	o << "cols: \"sol cost\" \"sol length\" "
	  << "\"nodes expanded\" \"nodes generated\" "
	  << "\"raw cpu time\"" << endl;

	do_output_recur(o, s);
}


