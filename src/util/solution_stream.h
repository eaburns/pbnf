/**
 * \file solution_stream.h
 *
 *
 *
 * \author eaburns
 * \date 2009-04-14
 */

#if !defined(_SOLUTION_STREAM_H_)
#define _SOLUTION_STREAM_H_

#include <queue>

#include "../state.h"
#include "timer.h"
#include "fixed_point.h"

using namespace std;

/**
 * Holds a stream of solutions along with the time at which the
 * solution was arrived.
 */
class SolutionStream {
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
	SolutionStream(Timer *t, double g);

	/**
	 * The destructor does nothing, but this gets rid of a
	 * warning.
	 */
	virtual ~SolutionStream() {}

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
	virtual fp_type see_solution(vector<State *> *path,
				     unsigned int gen,
				     unsigned int exp);

	/**
	 * Get the best solution path.
	 */
	vector<State *> *get_best_path(void);

	/**
	 * Output the solution stream to the given output stream.
	 */
	void output(ostream &o);

private:
	/**
	 * A solution cost and time pair.
	 */
	struct Solution {
		Solution(fp_type c, unsigned int l, unsigned int gen,
			 unsigned int exp, double t) {
			cost = c;
			length = l;
			generated = gen;
			expanded = exp;
			time = t;
		}
		fp_type cost;
		unsigned int length;
		unsigned int generated;
		unsigned int expanded;
		double time;
	};

	/** The current best solution path. */
	vector<State *> *best_path;

	/** The cost of the current best solution. */
	fp_type best_cost;

	/** The stream of solutions. */
	queue<Solution> solutions;

	/** The search timer */
	Timer *timer;

	/** The solution granularity. */
	fp_type granularity;
};

#endif /* !_SOLUTION_STREAM_H_ */
