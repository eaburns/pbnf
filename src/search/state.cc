/**
 * \file state.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <assert.h>

#include "state.h"

State::State(SearchDomain *d, State *parent, float g)
	: parent(parent), domain(d), g(g), h(-1), open(false) {}

State::~State() {}

/**
 * Get the search domain for this state.
 */
SearchDomain *State::get_domain(void) const
{
	return domain;
}

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
 * Set the g value for this state.
 */
void State::update(State *parent, float g)
{
	this->parent = parent;
	this->g = g;
}

/**
 * Get the estimated cost to go.
 * \return h
 */
float State::get_h(void) const
{
	assert(h >= 0.0);
	return h;
}

/**
 * Expand the given state.
 * \return A newly allocated vector of the children states.  This must
 *         be deleted by the caller.
 */
vector<State*> *State::expand(void)
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
vector<State *> *State::get_path(void)
{
	vector<State *> *path = new vector<State *>;
	State *p;
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

/**
 * Get the parent of this state.
 */
State *State::get_parent(void) const
{
	return parent;
}

/**
 * Set the open status of the state.
 */
void State::set_open(bool b)
{
	open = b;
}

/**
 * Test if the state is open.
 */
bool State::is_open(void) const
{
	return open;
}
