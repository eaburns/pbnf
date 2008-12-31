/* -*- mode:linux -*- */
/**
 * \file ida_star.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#include <vector>

#include "ida_star.h"
#include "cost_bound_dfs.h"

using namespace std;

vector<State *> *IDAStar::search(State *init)
{
	vector<State *> *path = NULL;
	float old_bound, bound = init->get_f();

	do {
		CostBoundDFS dfs(bound);
		cout << "bound=" << bound << endl;
		path = dfs.search(init->clone());
		set_expanded(get_expanded() + dfs.get_expanded());
		set_generated(get_generated() + dfs.get_generated());
		old_bound = bound;
		bound = dfs.get_min_pruned();
	} while ((!path || path->at(0)->get_g() > old_bound) && bound != -1);

	delete init;

	return path;
}
