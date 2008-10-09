/* -*- mode:linux -*- */
/**
 * \file grid_state.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <iostream>
#include <vector>

#include "grid_world.h"
#include "grid_state.h"

using namespace std;

/**
 * Create a new grid state.
 */
GridState::GridState(const GridWorld *d, const State *parent, int g, int x, int y)
	: State(d, parent, g), x(x), y(y)
{
	this->h = domain->get_heuristic()->compute(this);
}

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

/**
 * Create a copy of this state.
 */
State *GridState::clone(void) const
{
	const GridWorld *d = dynamic_cast<const GridWorld *>(domain);

	return new GridState(d, parent, g, x, y);
}

void GridState::print(ostream &o) const
{
	o << "x=" << x << ", y=" << y << ", g=" << g << ", h=" << h
	  << ", f=" << g + h << endl;
}

int GridState::get_x(void) const
{
	return x;
}

int GridState::get_y(void) const
{
	return y;
}
