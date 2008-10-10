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

vector<const State *> *IDAStar::search(const State *init)
{
	vector<const State *> *path = NULL;
	float bound = init->get_f();

	do {
		CostBoundDFS dfs(bound);

		path = dfs.search(init->clone());
		set_expanded(get_expanded() + dfs.get_expanded());
		set_generated(get_generated() + dfs.get_generated());
		bound = dfs.get_min_pruned();
	} while (!path && bound != -1);

	delete init;

	return path;
}
