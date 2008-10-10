/* -*- mode:linux -*- */
/**
 * \file cost_bound_dfs.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#include <vector>

#include "state.h"
#include "cost_bound_dfs.h"

CostBoundDFS::CostBoundDFS(float bound) : bound(bound), min_pruned(-1) {}

/**
 * A cost bounded DFS.
 */
vector<const State *> *CostBoundDFS::search(const State *init)
{
	vector<const State *> *path;
	vector<const State *> *children;

	if (init->get_f() > bound) {
		if (min_pruned == -1 || init->get_f() < min_pruned)
			min_pruned = init->get_f();
		delete init;
		return NULL;
	}

	if (init->is_goal()) {
		path = init->get_path();
		delete init;
		return path;
	}

	children = expand(init);
	if (!children)
		return NULL;

	for (unsigned int i = 0; i < children->size(); i += 1) {
		path = search(children->at(i));
		if (path) {
			for (i += 1; i < children->size(); i += 1)
				delete children->at(i);
			break;
		}
	}
	delete children;
	delete init;

	return path;
}

/**
 * Get the f(n) value of the minimum cost pruned node.
 */
float CostBoundDFS::get_min_pruned(void) const
{
	return min_pruned;
}
