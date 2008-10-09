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

ManhattanDist::ManhattanDist(int goal_x, int goal_y)
	: goal_x(goal_x), goal_y(goal_y) {}


/**
 * Compute the Manhattan distance heuristic.
 * \param state The state to comupte the heuristic for.
 * \return The Manhattan distance from the given state to the goal.
 */
float ManhattanDist::compute(const State *state) const
{
	const GridState *s;

	s = dynamic_cast<const GridState *>(state);
	return abs(s->get_x() - goal_x) + abs(s->get_y() - goal_y);
}
