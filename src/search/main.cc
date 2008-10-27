/* -*- mode:linux -*- */
/**
 * \file main.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <math.h>
#include <string.h>
#include <stdlib.h>

#include <iostream>
#include <vector>

#include "state.h"
#include "a_star.h"
#include "breadth_first_search.h"
#include "cost_bound_dfs.h"
#include "ida_star.h"
#include "kbfs.h"
#include "psdd/psdd.h"
#include "h_zero.h"
#include "grid/grid_world.h"

using namespace std;

// Globals -- ick.
unsigned int threads = 1;
float cost_bound = INFINITY;
float ratio = 1.0;

Search *get_search(int argc, char *argv[])
{
	if (argc > 1 && strcmp(argv[1], "astar") == 0) {
		return new AStar();
	} else if (argc > 1 && strcmp(argv[1], "idastar") == 0) {
		return new IDAStar();
	} else if (argc > 1 && sscanf(argv[1], "kbfs-%u", &threads) == 1) {
		return new KBFS(threads);
	} else if (argc > 1 && strcmp(argv[1], "bfs") == 0) {
		return new BreadthFirstSearch();
	} else if (argc > 1
		   && sscanf(argv[1], "costbounddfs-%f", &cost_bound) == 1) {
		return new CostBoundDFS(cost_bound);
	} else if (argc > 1
		   && sscanf(argv[1], "psdd-%u-%f", &threads, &ratio) == 1) {
		// order matters here... this has to be before the
		// less specific psdd-%u parsing which comes next.
		return new PSDD(threads);
	} else if (argc > 1 && sscanf(argv[1], "psdd-%u", &threads) == 1) {
		return new PSDD(threads);
	} else {
		cout << "Must supply a search algorithm:" << endl;
		cout << "\tastar" << endl
		     << "\tbfs" << endl
		     << "\tidastar" << endl
		     << "\tcostbounddfs-<cost>" << endl
		     << "\tkbfs-<threads>" << endl
		     << "\tpsdd-<threads>" << endl
		     << "\tpsdd-<threads>-<nblocks-per-thread>" << endl
		     << endl;
		exit(EXIT_FAILURE);
	}
}

int main(int argc, char *argv[])
{
	vector<const State *> *path;
	Search *search = get_search(argc, argv);
	GridWorld g(cin);

	if (ratio == 0)
		ratio = 1.0;
	unsigned int denom = g.get_height() / (ratio * threads);
	unsigned int nblocks = g.get_height() / denom;
	GridWorld::RowModProject project(&g, nblocks);
	g.set_projection(&project);

//	HZero hzero(&g);
//	g.set_heuristic(&hzero);
	GridWorld::ManhattanDist manhattan(&g);
	g.set_heuristic(&manhattan);

	path = search->search(g.initial_state());

	/* Print the graph to the terminal */
//	g.print(cout, path);

	cout << "generated: " << search->get_generated() << endl;
	cout << "expanded: " << search->get_expanded() << endl;
	if (path) {
		cout << "cost: " << path->at(0)->get_g() << endl;
		for (unsigned int i = 0; i < path->size(); i += 1)
			delete path->at(i);
		delete path;
	} else {
		cout << "No Solution" << endl;
	}

	delete search;

#if ENABLE_IMAGES
	g.export_eps("output.eps");
#endif	// ENABLE_IMAGES

	return EXIT_SUCCESS;
}
