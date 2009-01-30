/**
 * \file get_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-13
 */

#include <string.h>
#include <stdlib.h>

#include <limits>
#include <iostream>

#include "a_star.h"
#include "multi_a_star.h"
#include "breadth_first_search.h"
#include "cost_bound_dfs.h"
#include "ida_star.h"
#include "kbfs.h"
#include "psdd_search.h"
#include "bfpsdd_search.h"
#include "idpsdd_search.h"
#include "dynamic_bounded_psdd.h"
#include "pbnf_search.h"
#include "pastar.h"
#include "prastar.h"

#include "get_search.h"

using namespace std;

unsigned int threads = 1;
fp_type cost_bound = fp_infinity;
unsigned int nblocks = 1;
float weight = 1.0;

Search *get_search(int argc, char *argv[])
{
	unsigned int min_expansions = 0;
	unsigned int multiplier;

	if (argc > 1 && strcmp(argv[1], "astar") == 0) {
		return new AStar();
	} else if (argc > 1 && strcmp(argv[1], "idastar") == 0) {
		return new IDAStar();
	} else if (argc > 1 && strcmp(argv[1], "bfs") == 0) {
		return new BreadthFirstSearch();
	} else if (argc > 1
		   && sscanf(argv[1], "costbounddfs-%ju", &cost_bound) == 1) {
		return new CostBoundDFS(cost_bound);
	} else if (argc > 1 && sscanf(argv[1], "kbfs-%u", &threads) == 1) {
		return new KBFS(threads);
	} else if (argc > 1 && sscanf(argv[1], "pastar-%u", &threads) == 1) {
		return new PAStar(threads);
	} else if (argc > 1 && sscanf(argv[1], "prastar-%u-%u", &threads, &nblocks) == 2) {
		return new PRAStar(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "psdd-%u-%u", &threads, &nblocks) == 2) {
		return new PSDDSearch(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "bfpsdd-%u-%u-%u-%u", &multiplier,
			     &min_expansions, &threads, &nblocks) == 4) {
		return new BFPSDDSearch(threads, multiplier, min_expansions);
	} else if (argc > 1
		   && sscanf(argv[1], "idpsdd-%u-%u", &threads, &nblocks) == 2) {
		return new IDPSDDSearch(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "dynpsdd-%f-%u-%u",
			     &weight, &threads, &nblocks) == 3) {
		return new DynamicBoundedPSDD(threads, weight);
	} else if (argc > 1
		   && sscanf(argv[1], "pbnf-%f-%u-%u-%u",
			     &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new PBNFSearch(threads, min_expansions, false);
	} else if (argc > 1
		   && sscanf(argv[1], "safepbnf-%f-%u-%u-%u", &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new PBNFSearch(threads, min_expansions, true);
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
		     << "\tprastar-<threads>-<nblocks>" << endl
		     << "\tpsdd-<threads>-<nblocks>" << endl
		     << "\tdynpsdd-<weight>-<threads>-<nblocks>" << endl
		     << "\tbfpsdd-<multiplier>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tidpsdd-<threads>-<nblocks>" << endl
		     << "\tpbnf-<weight>-<min_expansions>-<threads>-<nblocks>" << endl
		     << "\tsafepbnf-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tsafepbnf-<weight>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tmultiastar-<threads>" << endl
		     << endl;
		exit(EXIT_FAILURE);
	}
}
