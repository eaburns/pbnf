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
#include "state.h"
#include "search.h"
#include "closed_list.h"

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
	SolutionStream *solutions;
	ClosedList closed;
	vector<double> *weights;
};

#endif	/* !_ARASTAR_H_ */
