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
#include <vector>

#include <stdlib.h>

#include "state.h"
#include "a_star.h"
#include "grid/manhattan_dist.h"
#include "grid/grid_world.h"

using namespace std;

int main(void)
{
	vector<const State *> *path;
	GridWorld g(cin);
	ManhattanDist h(g.get_goal_x(), g.get_goal_y());
	AStar astar;

	g.set_heuristic(&h);

	path = astar.search(g.initial_state());
	g.print(cout, path);

	if (path) {
		for (unsigned int i = 0; i < path->size(); i += 1)
			delete path->at(i);
		delete path;
	}

	return EXIT_SUCCESS;
}
