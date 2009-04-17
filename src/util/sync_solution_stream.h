/**
 * \file sync_solution_stream.h
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */
#if !defined(_SYNC_SOLUTION_STREAM_H_)
#define _SYNC_SOLUTION_STREAM_H_

#include <pthread.h>

#include <queue>

#include "../state.h"
#include "solution_stream.h"
#include "timer.h"
#include "fixed_point.h"

using namespace std;

/**
 * Holds a stream of solutions along with the time at which the
 * solution was arrived.
 */
class SyncSolutionStream : public SolutionStream {
public:
	/**
	 * Create a new solution stream that uses the given timer and
	 * that tracks solutions that are at least the given
	 * granularity better than the previous solution.
	 *
	 * \param g The solution granularity.  A new solution is added
	 *          to the stream if it is at least [g] times better
	 *          than the current best solution.
	 */
	SyncSolutionStream(Timer *t, double g);

	/**
	 * See an incumbent solution.
	 *
	 * \param gen Nodes generated at the time the solution was found.
	 *
	 * \param exp Nodes expanded at the time the solution was found.
	 *
	 * \return The new pruning bound (may be the same if the
	 *         incumbent turns out to be worse than the current
	 *         incumbent).
	 */
	fp_type see_solution(vector<State *> *path,
			     unsigned int gen,
			     unsigned int exp);

private:
	pthread_mutex_t mutex;
};

#endif /* !_SYNC_SOLUTION_STREAM_H_ */