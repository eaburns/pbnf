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
	: State(parent, g), d(d), x(x), y(y)
{
	this->h = d->h_val(this);
}

/**
 * Test if this state is the goal.
 */
bool GridState::is_goal(void) const
{
	return d->get_goal_x() == x && d->get_goal_y() == y;
}

/**
 * Expand the given state.
 */
vector<const State*> *GridState::expand(const State *s) const
{
	return d->expand(s);
}

/**
 * Get the hash value of this state.
 */
int GridState::hash(void) const
{
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
