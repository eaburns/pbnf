/* -*- mode:linux -*- */
/**
 * \file main.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <iostream>

#include <stdlib.h>

#include "grid/manhattan_dist.h"
#include "grid/grid_world.h"

using namespace std;

int main(void)
{
	GridWorld g(cin);
	ManhattanDist h(g.get_goal_x(), g.get_goal_y());

	g.set_heuristic(&h);

	return EXIT_SUCCESS;
}
