/* -*- mode:linux -*- */
/**
 * \file manhattan_dist.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include "manhattan_dist.h"
#include "grid_state.h"
#include "grid_world.h"

ManhattanDist::ManhattanDist(const GridWorld *d)
	: d(d) {}

float ManhattanDist::compute(const State *state) const
{
	const GridState *s;

	return abs(s->get_x() - d->get_goal_x())
		+ abs(s->get_y() - d->get_goal_y());
}
