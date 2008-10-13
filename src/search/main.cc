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
#include "cost_bound_dfs.h"
#include "ida_star.h"
#include "grid/manhattan_dist.h"
#include "grid/grid_world.h"

using namespace std;

int main(void)
{
	vector<const State *> *path;
	GridWorld g(cin);
	ManhattanDist h(g.get_goal_x(), g.get_goal_y());
//	CostBoundDFS search(23);
	AStar search;
//	IDAStar search;

	g.set_heuristic(&h);

	path = search.search(g.initial_state());
//	g.print(cout, path);

	cout << "generated: " << search.get_generated() << endl;
	cout << "expanded: " << search.get_expanded() << endl;
	if (path) {
		cout << "cost: " << path->at(0)->get_g() << endl;
		for (unsigned int i = 0; i < path->size(); i += 1)
			delete path->at(i);
		delete path;
	}

	g.export_eps("output.eps");

	return EXIT_SUCCESS;
}
