/* -*- mode:linux -*- */
/**
 * \file breadth_first_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-25
 */

#if !defined(_BREADTH_FIRST_SEARCH_H_)
#define _BREADTH_FIRST_SEARCH_H_

#include <vector>

#include "state.h"
#include "search.h"

using namespace std;

class BreadthFirstSearch : public Search {
public:
	BreadthFirstSearch(void);

	BreadthFirstSearch(float bound);

	virtual ~BreadthFirstSearch(void);

	virtual vector<const State *> *search(const State *);

private:
	float bound;
};

#endif	/* !_BREADTH_FIRST_SEARCH_H_ */
