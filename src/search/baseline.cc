/* -*- mode:linux -*- */
/**
 * \file baseline.cc
 *
 * This file contains the code for getting a baseline to compare
 * against.  The idea is to run parallel A*s with an increasing thread
 * count (to a specified limit).  Ideally, the speedup should be
 * linear with the number of threads.  This isn't really possible,
 * however, so the actual results will give us an idea of the
 * ``ideal'' speedup that is achievable by the machine that we are
 * running on.
 *
 * \author Ethan Burns
 * \date 2008-10-31
 */

#include <sys/time.h>

#include <assert.h>
#include <stdlib.h>
#include <time.h>

#include <iostream>
#include <fstream>
#include <string>

#include "state.h"
#include "search_domain.h"
#include "heuristic.h"
#include "a_star.h"
#include "util/thread.h"
#include "util/timer.h"
#include "grid/grid_world.h"

using namespace std;

class AStarThread : public Thread {
public:
	AStarThread(string map) {
		ifstream fin(map.c_str(), ifstream::in);

		g = new GridWorld(fin);
		fin.close();
	}

	~AStarThread(void) {
		delete g;
	}

	void run(void) {
		vector<const State *> *path;
		AStar search;
		GridWorld::ManhattanDist manhattan(g);
		g->set_heuristic(&manhattan);

		path = search.search(g->initial_state());
		assert(path);
//		cout << "Path cost: " << path->at(0)->get_g() << endl;
		delete path;
	}

private:
	GridWorld *g;
};


/**
 * Print the usage.
 */
void usage(void)
{
	cout << "Usage:" << endl
	     << "\tbaseline <max_threads> <grid_map>" << endl;
	exit(EXIT_FAILURE);
}

/**
 * Perform max_thread number of parallel A*s.
 */
void do_one_search(string map, unsigned int max_thread)
{
	vector<Thread *> threads;

	for (unsigned int i = 0; i < max_thread; i += 1)
		threads.push_back(new AStarThread(map));

	for (unsigned int i = 0; i < max_thread; i += 1)
		threads[i]->start();

	for (unsigned int i = 0; i < max_thread; i += 1) {
		threads[i]->join();
		delete threads[i];
	}
}

/**
 * Preform a sequence of increasing parallel A*s and print timing
 * information for each.
 */
void do_searches(string map, unsigned int max_threads, unsigned int step)
{
	double diff;
	Timer t;

	cout << "Threads, Real Time (sec) per Thread" << endl;
	for (unsigned int i = 1; i <= max_threads; i += step) {
		t.start();
		do_one_search(map, i);
		diff = t.stop();

		cout << i << ", " << diff/i << endl;
	}
}

int main(int argc, char *argv[])
{
	char *endp;
	long max_threads;
	unsigned int step = 1;

	if (argc < 3)
		usage();

	max_threads = strtol(argv[1], &endp, 0);
	if (endp[0] != '\0') {
		cout << "Bad number: " << argv[1] << endl;
		usage();
	}

	do_searches(argv[2], max_threads, step);

	return EXIT_SUCCESS;
}
