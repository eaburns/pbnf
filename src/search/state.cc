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

int State::get_g(void) const
{
	return g;
}

int State::get_h(void) const
{
	return h;
}

/**
 * Expand the given state.
 */
vector<const State*> *State::expand(void) const
{

	return domain->expand(this);
}

/**
 * Follow the parent links back up and create copies of each state.
 * \return A path from the initial state to the goal state.
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
