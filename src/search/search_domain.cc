/* -*- mode:linux -*- */
/**
 * \file search_domain.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <assert.h>

#include "search_domain.h"

/**
 * Create a new search domain.
 */
SearchDomain::SearchDomain() : heuristic(NULL) {}

/**
 * Set the heuristic that will be used in this domain.
 */
void SearchDomain::set_heuristic(const Heuristic *h)
{
	this->heuristic = h;
}

/**
 * Compute the heuristic for the given state.
 */
float SearchDomain::h_val(const State *s) const
{
	assert(heuristic != NULL);

	return heuristic->compute(s);
}
