/**
 * \file arastar.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-20
 */
#include <assert.h>

#include <vector>
#include <iostream>

using namespace std;

#include "util/fixed_point.h"
#include "util/serial_solution_stream.h"
#include "state.h"
#include "pq_open_list.h"
#include "closed_list.h"
#include "arastar.h"

ARAStar::ARAStar(vector<double> *ws)
	: solutions(NULL),
	  weights(ws),
	  heuristic(NULL),
	  next_weight(1),
	  cur_weight(ws->at(0))
{
}

ARAStar::~ARAStar(void)
{
	closed.delete_all_states();
}


/**
 * Perform an A* search.
 */
vector<State *> *ARAStar::search(Timer *t, State *init)
{
	fp_type incumbent_cost = fp_infinity;

	heuristic = init->get_domain()->get_heuristic();
	next_weight = 1;
	cur_weight = heuristic->get_weight();

	solutions = new SerialSolutionStream(t, 0.0001);
	open.add(init);

	while (!open.empty() || !incons.empty()) {
		if (open.empty()) {
			if (!solutions->get_best_path())
				return NULL;
			else {
#if !defined(NDEBUG)
				cout << "No Solution found at weight "
				     << weights->at(next_weight - 1)
				     << endl;
#endif	// !NDEBUG
				move_to_next_weight();
			}
		}


		State *s = open.take();
		if (s->get_f_prime() >= incumbent_cost) {
#if !defined(NDEBUG)
			cout << "No Solution found at weight "
			     << weights->at(next_weight - 1)
			     << endl;
#endif	// !NDEBUG
			move_to_next_weight();
			continue;
		}

		if (s->get_f() >= incumbent_cost)
			continue;

		if (s->is_goal()) {
			vector<State*> *path = s->get_path();
			solutions->see_solution(path,
						get_generated(),
						get_expanded());
#if !defined(NDEBUG)
			cout << "Solution of cost " << path->at(0)->get_g() / fp_one
			     << " found at weight " << weights->at(next_weight - 1)
			     << endl;
#endif	// !NDEBUG
			if (cur_weight == 1.0)
				return path;

			move_to_next_weight();
			incumbent_cost = s->get_g();
		}

		vector<State *> *children = expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			State *c = children->at(i);
			State *dup = closed.lookup(c);
			if (dup) {
				if (dup->get_g() > c->get_g()) {
					dup->update(c->get_parent(), c->get_c(), c->get_g());
					if (dup->is_open())
						open.see_update(dup);
					else
						incons.add(dup);
				}
				delete c;
			} else {
				open.add(c);
				closed.add(c);
			}

		}
		delete children;
	}

	return solutions->get_best_path();
}

void ARAStar::output_stats(void)
{
	if (solutions)
		solutions->output(cout);
}

void ARAStar::move_to_next_weight()
{
	double wt = 1.0;
	if (next_weight == weights->size()) {
		cerr << "Final weight in sched is not 1.0"
		     << endl;
	} else {
		wt = weights->at(next_weight);
		next_weight += 1;
	}

	cur_weight = wt;
	heuristic->set_weight(wt);

	open.resort();
	incons.re_open(&open);
	closed.remove_closed_nodes();
}
