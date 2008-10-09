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
	: parent(parent), domain(d), g(g)
{
	this->h = d->get_heuristic()->compute(this);
}

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
vector<const State*> *State::expand(const State *s) const{

	return domain->expand(s);
}
