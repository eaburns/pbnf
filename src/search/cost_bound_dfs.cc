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

CostBoundDFS::CostBoundDFS(float bound) : bound(bound) {}

/**
 * A cost bounded DFS.
 */
vector<const State *> *CostBoundDFS::search(const State *init)
{
	vector<const State *> *path;
	vector<const State *> *children;

	if (init->get_f() > bound) {
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
