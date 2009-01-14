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
vector<State *> *CostBoundDFS::search(State *init)
{
	vector<State *> *path = NULL;
	vector<State *> *children;

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
		if (is_cycle(children->at(i))) {
		    delete children->at(i);
		    continue;
		}
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

/**
 * Check if this state is a parent of itself, in which case, it is a
 * cycle and we can prune.
 * \param s The state.
 * \return True if this state is on the path to itself.
 */
bool CostBoundDFS::is_cycle(State *s) const
{
	State *p;

	for (p = s->get_parent(); p; p = p->get_parent())
		if (p->equals(s))
			return true;

	return false;
}
