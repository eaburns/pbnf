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
#include <vector>
#include <iostream>

// this has to come first because other includes may include the C++
// STL map.
#include "lpastar.h"

#include "a_star.h"
#include "arastar.h"
#include "awastar.h"
#include "multi_a_star.h"
#include "breadth_first_search.h"
#include "cost_bound_dfs.h"
#include "ida_star.h"
#include "kbfs.h"
#include "psdd_search.h"
#include "arpbnf_search.h"
#include "opbnf_search.h"
#include "bfpsdd_search.h"
#include "wbfpsdd_search.h"
#include "idpsdd_search.h"
#include "dynamic_bounded_psdd.h"
#include "pbnf_search.h"
#include "wpbnf_search.h"
#include "pastar.h"
#include "prastar.h"
#include "wprastar.h"

#include "get_search.h"

#include <limits.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#if !defined(LINE_MAX)
#define LINE_MAX 255
#endif

using namespace std;

unsigned int threads = 1;
fp_type cost_bound = fp_infinity;
unsigned int nblocks = 1;
float weight = 1.0;

/**
 * Parse a weight schedule string.
 */
vector<double> *parse_weights(char *str)
{
	unsigned int i, j;
	bool decimal_seen = false;
	char buf[LINE_MAX];
	vector<double> *weights = new vector<double>();

	j = 0;
	for (i = 0; i < strlen(str); i += 1) {
		char c = str[i];
		if (isdigit(c) || (c == '.' && !decimal_seen)) {
			if (c == '.')
				decimal_seen = true;
			assert(j < LINE_MAX); // just bomb out if we overflow :(
			buf[j] = c;
			j += 1;
		} else if (c == ',') {
			double d;

			assert(j < LINE_MAX); // just bomb out if we overflow :(
			buf[j] = '\0';
			j = 0;
			decimal_seen = false;

			sscanf(buf, "%lf", &d);
			weights->push_back(d);
		} else {
			cerr << "Invalid weight list [" << str
			     << "] at char: " << i << endl;
			exit(1);
		}
	}
	if (j > 0) {
		double d;
		buf[j] = '\0';
		j = 0;
		sscanf(buf, "%lf", &d);
		weights->push_back(d);
	}

	return weights;
}

Search *get_search(int argc, char *argv[])
{
	unsigned int min_expansions = 0;
	unsigned int multiplier;

	if (argc > 1 && strcmp(argv[1], "astar") == 0) {
		return new AStar();
	} else if (argc > 1 && sscanf(argv[1], "wastar-%f", &weight) == 1) {
		return new AStar(false);
	} else if (argc > 1 && sscanf(argv[1], "wastardd-%f", &weight) == 1) {
		return new AStar(true);
	} else if (argc > 1 && sscanf(argv[1], "awastar-%f", &weight) == 1) {
		return new AwAStar();
	} else if (argc > 2 && strcmp(argv[1], "arastar") == 0) {
		vector<double> *weights = parse_weights(argv[2]);
		weight = weights->at(0);
		return new ARAStar(weights);
	} else if (argc > 1 && strcmp(argv[1], "idastar") == 0) {
		return new IDAStar();
	} else if (argc > 1 && strcmp(argv[1], "bfs") == 0) {
		return new BreadthFirstSearch();
/*
	} else if (argc > 1
		   && sscanf(argv[1], "costbounddfs-%lf", &cost_bound) == 1) {
		return new CostBoundDFS(cost_bound);
*/
	} else if (argc > 1 && sscanf(argv[1], "kbfs-%u", &threads) == 1) {
		return new KBFS(threads);
	} else if (argc > 1 && sscanf(argv[1], "pastar-%u", &threads) == 1) {
		return new PAStar(threads);
	} else if (argc > 1 && sscanf(argv[1], "lpastar-%u", &threads) == 1) {
		return new LPAStar(threads);
	} else if (argc > 1 && sscanf(argv[1], "prastar-%u-%u", &threads, &nblocks) == 2) {
		return new PRAStar(threads);
	} else if (argc > 1 && sscanf(argv[1], "wprastar-%f-%u-%u", &weight, &threads, &nblocks) == 3) {
		return new wPRAStar(threads, false);
	} else if (argc > 1 && sscanf(argv[1], "wprastardd-%f-%u-%u", &weight, &threads, &nblocks) == 3) {
		return new wPRAStar(threads, true);
	} else if (argc > 1
		   && sscanf(argv[1], "psdd-%u-%u", &threads, &nblocks) == 2) {
		return new PSDDSearch(threads);
	} else if (argc > 1
		   && sscanf(argv[1], "bfpsdd-%u-%u-%u-%u", &multiplier,
			     &min_expansions, &threads, &nblocks) == 4) {
		return new BFPSDDSearch(threads, multiplier, min_expansions);
	} else if (argc > 1
		   && sscanf(argv[1], "wbfpsdd-%f-%u-%u-%u-%u", &weight,
			     &multiplier, &min_expansions,
			     &threads, &nblocks) == 5) {
		return new WBFPSDDSearch(threads, multiplier, min_expansions, false);
	} else if (argc > 1
		   && sscanf(argv[1], "wbfpsdddd-%f-%u-%u-%u-%u", &weight,
			     &multiplier, &min_expansions,
			     &threads, &nblocks) == 5) {
		return new WBFPSDDSearch(threads, multiplier, min_expansions, true);
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
		return new PBNF::PBNFSearch(threads, min_expansions, false);
	} else if (argc > 1
		   && sscanf(argv[1], "safepbnf-%f-%u-%u-%u", &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new PBNF::PBNFSearch(threads, min_expansions, true);
	} else if (argc > 2
		   && sscanf(argv[1], "arpbnf-%u-%u-%u", &min_expansions, &threads, &nblocks) == 3) {
		vector<double> *weights = parse_weights(argv[2]);
		weight = weights->at(0);
		return new ARPBNF::ARPBNFSearch(threads, min_expansions, false, weights);
	} else if (argc > 2
		   && sscanf(argv[1], "iarpbnf-%u-%u-%u", &min_expansions, &threads, &nblocks) == 3) {
		vector<double> *weights = parse_weights(argv[2]);
		weight = weights->at(0);
		return new ARPBNF::ARPBNFSearch(threads, min_expansions, true, weights);
	} else if (argc > 1
		   && sscanf(argv[1], "wpbnf-%f-%u-%u-%u", &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new WPBNF::WPBNFSearch(threads, min_expansions, false);
	} else if (argc > 1
		   && sscanf(argv[1], "wpbnfdd-%f-%u-%u-%u", &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new WPBNF::WPBNFSearch(threads, min_expansions, true);
	} else if (argc > 1
		   && sscanf(argv[1], "opbnf-%f-%u-%u-%u", &weight, &min_expansions, &threads, &nblocks) == 4) {
		return new OPBNF::OPBNFSearch(threads, min_expansions);
	} else if (argc > 1 && sscanf(argv[1], "multiastar-%u", &threads) == 1) {
		return new MultiAStar(threads);
	} else if (argc > 1 && sscanf(argv[1], "multiwastar-%f-%u", &weight, &threads) == 2) {
		return new MultiAStar(threads);
	} else {
		cout << "Must supply a search algorithm:" << endl;
		cout << "\tastar" << endl
		     << "\twastar-<weight>" << endl
		     << "\tidastar" << endl
		     << "\tbfs" << endl
		     << "\tcostbounddfs-<cost>" << endl
		     << "\tkbfs-<threads>" << endl
		     << "\tawastar-<weight>" << endl
		     << "\tarastar <weight-list>" << endl
		     << "\tpastar-<threads>" << endl
		     << "\tprastar-<threads>-<nblocks>" << endl
		     << "\twprastar-<weight>-<threads>-<nblocks>" << endl
		     << "\twprastardd-<weight>-<threads>-<nblocks>" << endl
		     << "\tpsdd-<threads>-<nblocks>" << endl
		     << "\tdynpsdd-<weight>-<threads>-<nblocks>" << endl
		     << "\tbfpsdd-<multiplier>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\twbfpsdd-<weight>-<multiplier>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\twbfpsdddd-<weight>-<multiplier>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tidpsdd-<threads>-<nblocks>" << endl
		     << "\tpbnf-<weight>-<min_expansions>-<threads>-<nblocks>" << endl
		     << "\twpbnf-<weight>-<min_expansions>-<threads>-<nblocks>" << endl
		     << "\twpbnfdd-<weight>-<min_expansions>-<threads>-<nblocks>" << endl
		     << "\tsafepbnf-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tsafepbnf-<weight>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tarpbnf-<min-expansions>-<threads>-<nblocks> <weight-list>" << endl
		     << "\topbnf-<bound>-<min-expansions>-<threads>-<nblocks>" << endl
		     << "\tmultiastar-<threads>" << endl
		     << "\tmultiwastar-<weight>-<threads>" << endl
		     << endl;
		exit(EXIT_FAILURE);
	}
}
