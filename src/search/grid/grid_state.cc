/* -*- mode:linux -*- */
/**
 * \file grid_state.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <vector>

#include "grid_world.h"
#include "grid_state.h"

using namespace std;

/**
 * Create a new grid state.
 */
GridState::GridState(const GridWorld *d, const State *parent, int g, int x, int y)
	: State(d, parent, g), x(x), y(y) {}

/**
 * Test if this state is the goal.
 */
bool GridState::is_goal(void) const
{
	const GridWorld *d;

	d = dynamic_cast<const GridWorld *>(domain);

	return d->get_goal_x() == x && d->get_goal_y() == y;
}

/**
 * Get the hash value of this state.
 */
int GridState::hash(void) const
{
	const GridWorld *d;

	d = dynamic_cast<const GridWorld *>(domain);

	return x * d->get_height() + y;
}

int GridState::get_x(void) const
{
	return x;
}

int GridState::get_y(void) const
{
	return y;
}
