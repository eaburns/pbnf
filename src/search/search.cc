/* -*- mode:linux -*- */
/**
 * \file search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <vector>

#include "state.h"
#include "search.h"

Search::Search(void) : expanded(0), generated(0) {}

vector<const State *> *Search::expand(const State *s)
{
	vector<const State *> *children;

	children = s->expand();
	expanded += 1;
	generated += children->size();

	return children;
}

void Search::clear_counts(void)
{
	expanded = generated = 0;
}

unsigned long Search::get_expanded(void) const
{
	return expanded;
}

unsigned long Search::get_generated(void) const
{
	return generated;
}
