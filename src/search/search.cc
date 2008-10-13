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

/**
 * Call the expand method of the given state and track stats on number
 * of generated/expanded nodes.
 * \param s The state to expand.
 * \return A newly allocated vector of the children states.  This must
 *         be deleted by the caller.
 */
vector<const State *> *Search::expand(const State *s)
{
	vector<const State *> *children;

	children = s->expand();
	expanded += 1;
	generated += children->size();

	return children;
}

/**
 * Clear the expanded and generated counters.
 */
void Search::clear_counts(void)
{
	expanded = generated = 0;
}

/**
 * Get the value of the expanded counter.
 */
unsigned long Search::get_expanded(void) const
{
	return expanded;
}

/**
 * Get the value of the generated counter.
 */
unsigned long Search::get_generated(void) const
{
	return generated;
}

/**
 * Set the expanded count.
 * \param e The value to set it to.
 */
void Search::set_expanded(unsigned long e)
{
	expanded = e;
}

/**
 * Set the generated count.
 * \param g The value to set it to.
 */
void Search::set_generated(unsigned long g)
{
	generated = g;
}