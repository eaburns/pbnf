/* -*- mode:linux -*- */
/**
 * \file search_domain.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include "search_domain.h"

/**
 * Create a new search domain.
 */
SearchDomain::SearchDomain(const Heuristic *h)
	: h(h) {}

/**
 * Compute the heuristic for the given state.
 */
float SearchDomain::h_val(const State *s) const
{
	return h->compute(s);
}
