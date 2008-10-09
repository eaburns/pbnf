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

void State::set_parent(const State *p)
{
	parent = p;
}

const State *State::get_parent(void) const
{
	return parent;
}
