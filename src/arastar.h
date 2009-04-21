/**
 * \file arastar.h
 *
 *
 *
 * \author eaburns
 * \date 2009-04-20
 */
#if !defined(_ARASTAR_H_)
#define _ARASTAR_H_

#include <vector>

using namespace std;

#include "util/solution_stream.h"
#include "pq_open_list.h"
#include "state.h"
#include "search.h"
#include "closed_list.h"
#include "incons_list.h"

/**
 * An A* search class.
 */
class ARAStar : public Search {
public:
	ARAStar(vector<double> *weights);
	virtual ~ARAStar(void);
	virtual vector<State *> *search(Timer *, State *);
	void output_stats(void);
private:
	void move_to_next_weight();

	SolutionStream *solutions;
	PQOpenList<State::PQOpsFPrime> open;
	ClosedList closed;
	InconsList incons;
	vector<double> *weights;


	Heuristic *heuristic;
	unsigned int next_weight;
	double cur_weight;
};

#endif	/* !_ARASTAR_H_ */
