/* -*- mode:linux -*- */
/**
 * \file state.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include "state.h"

State::State(const SearchDomain *d, const State *parent, int g)
	: parent(parent), domain(d), g(g), h(-1) {}

/**
 * Get the estimated cost of a path that uses this node.
 * \return g + h
 */
float State::get_f(void) const
{
	return g + h;
}

/**
 * Get the cost so far of the state.
 * \return g
 */
float State::get_g(void) const
{
	return g;
}

/**
 * Get the estimated cost to go.
 * \return h
 */
float State::get_h(void) const
{
	return h;
}

/**
 * Expand the given state.
 * \return A newly allocated vector of the children states.  This must
 *         be deleted by the caller.
 */
vector<const State*> *State::expand(void) const
{

	return domain->expand(this);
}

/**
 * Follow the parent links back up and create copies of each state.
 * \return A path from the initial state to the goal state.  This
 *         vector and the states within it must be deleted by the
 *         caller.  All of the states on the returned path are clones
 *         of the states from the search, so those states can be
 *         deleted separately.
 */
vector<const State *> *State::get_path(void) const
{
	vector<const State *> *path = new vector<const State *>;
	const State *p;
	State *copy, *last = NULL;

	for (p = this; p; p = p->parent) {
		copy = p->clone();
		copy->parent = NULL;

		if (last)
			last->parent = copy;

		path->push_back(copy);
		last = copy;
	}

	return path;
}
