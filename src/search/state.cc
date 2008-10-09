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

State::State(const State *parent, int g)
	: parent(parent), g(g) {}

int State::get_g(void) const
{
	return g;
}

int State::get_h(void) const
{
	return h;
}

