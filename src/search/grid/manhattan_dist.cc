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

ManhattanDist::ManhattanDist(const SearchDomain *d) : Heuristic(d) {}

/**
 * Compute the Manhattan distance heuristic.
 * \param state The state to comupte the heuristic for.
 * \return The Manhattan distance from the given state to the goal.
 */
float ManhattanDist::compute(const State *state) const
{
	const GridState *s;
	const GridWorld *w;

	s = dynamic_cast<const GridState *>(state);
	w = dynamic_cast<const GridWorld *>(domain);
	if (w->get_cost_type() == GridWorld::UNIT_COST) {
		return abs(s->get_x() - w->get_goal_x())
			+ abs(s->get_y() - w->get_goal_y());
	} else {		// Life-cost
		float x_cost = abs(s->get_x() - w->get_goal_x())
			* s->get_y();
		float y_cost = 0.0;

		unsigned int min_y = s->get_y() < w->get_goal_y()
			? s->get_y()
			: w->get_goal_y();
		unsigned int max_y = s->get_y() > w->get_goal_y()
			? s->get_y()
			: w->get_goal_y();
		for (unsigned int i = min_y; i < max_y; i += 1)
			y_cost += i;

		return x_cost + y_cost;
	}
}
