/**
 * \file heuristic.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-13
 */

#include "util/fixed_point.h"

#include "heuristic.h"

Heuristic::Heuristic(const SearchDomain *d) : domain(d), weight(fp_one) {}

Heuristic::~Heuristic() {}

void Heuristic::set_weight(float weight)
{
	weight = fp_one * weight;
}

fp_type Heuristic::get_weight(void) const
{
	return weight;
}
