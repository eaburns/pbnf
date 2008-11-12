/* -*- mode:linux -*- */
/**
 * \file tiles_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-11
 */

#define _POSIX_C_SOURCE 200112L

#include <math.h>
#include <string.h>
#include <stdlib.h>

#include <iostream>
#include <vector>

#include "state.h"
#include "a_star.h"
#include "multi_a_star.h"
#include "breadth_first_search.h"
#include "cost_bound_dfs.h"
#include "ida_star.h"
#include "kbfs.h"
#include "psdd_search.h"
#include "dynamic_bounded_psdd.h"
#include "pbnf_search.h"
#include "h_zero.h"
#include "tiles/tiles.h"
#include "pastar.h"
#include "util/timer.h"

using namespace std;

// Globals -- ick.
unsigned int threads = 1;
float cost_bound = INFINITY;
float ratio = 1.0;
float weight = 1.0;

Search *get_search(int argc, char *argv[])
{
	if (argc > 1 && strcmp(argv[1], "astar") == 0) {
		return new AStar();
	} else if (argc > 1 && strcmp(argv[1], "idastar") == 0) {
		return new IDAStar();
	} else if (argc > 1 && strcmp(argv[1], "bfs") == 0) {
		return new BreadthFirstSearch();
	} else if (argc > 1
		   && sscanf(argv[1], "costbounddfs-%f", &cost_bound) == 1) {
		return new CostBoundDFS(cost_bound);
	} else if (argc > 1 && sscanf(argv[1], "kbfs-%u", &threads) == 1) {
		return new KBFS(threads);
	} else if (argc > 1 && sscanf(argv[1], "pastar-%u", &threads) == 1) {
		return new PAStar(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "psdd-%u-%f", &threads, &ratio) == 2) {
		return new PSDDSearch(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "dynpsdd-%u-%f-%f",
			     &threads, &ratio, &weight) == 3) {
		return new DynamicBoundedPSDD(threads, weight);
	} else if (argc > 1
		   && sscanf(argv[1], "pbnf-%u-%f", &threads, &ratio) == 2) {
		return new PBNFSearch(threads);
	} else if (argc > 1 && sscanf(argv[1], "multiastar-%u", &threads) == 1) {
		return new MultiAStar(threads);
	} else {
		cout << "Must supply a search algorithm:" << endl;
		cout << "\tastar" << endl
		     << "\tidastar" << endl
		     << "\tbfs" << endl
		     << "\tcostbounddfs-<cost>" << endl
		     << "\tkbfs-<threads>" << endl
		     << "\tpastar-<threads>" << endl
		     << "\tpsdd-<threads>-<nblocks/thread>" << endl
		     << "\tdynpsdd-<threads>-<nblocks/thread>-<weight>" << endl
		     << "\tpbnf-<threads>-<nblocks/thread>" << endl
		     << "\tmultiastar-<threads>" << endl
		     << endl;
		exit(EXIT_FAILURE);
	}
}

int main(int argc, char *argv[])
{
	vector<const State *> *path;
	Search *search = get_search(argc, argv);
	Tiles g(cin);
	Timer timer;

/*
	if (ratio == 0)
		ratio = 1.0;
	int denom = g.get_height() / ((int) ratio * threads);
	unsigned int nblocks = g.get_height() / denom;
	GridWorld::RowModProject project(&g, nblocks);
	g.set_projection(&project);
*/

//	HZero hzero(&g);
//	g.set_heuristic(&hzero);
	Tiles::ManhattanDist manhattan(&g);
	g.set_heuristic(&manhattan);

	timer.start();
	path = search->search(g.initial_state());
	timer.stop();

	/* Print the graph to the terminal */
//	g.print(cout, path);

	if (path) {
		cout << "cost: " << (int) path->at(0)->get_g() << endl;
		cout << "length: " << path->size() << endl;
		for (unsigned int i = 0; i < path->size(); i += 1)
			delete path->at(i);
		delete path;
	} else {
		cout << "No Solution" << endl;
	}
	cout << "wall_time: " << timer.get_wall_time() << endl;
	cout << "CPU_time: " << timer.get_processor_time() << endl;
	cout << "generated: " << search->get_generated() << endl;
	cout << "expanded: " << search->get_expanded() << endl;

	delete search;

	return EXIT_SUCCESS;
}
