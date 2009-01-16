/**
 * \file h_zero.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-13
 */

#include "h_zero.h"

HZero::HZero(const SearchDomain *d) : Heuristic(d) {}

fp_type HZero::compute(State *s) const
{
	return 0.0;
}
