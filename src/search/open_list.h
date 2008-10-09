/* -*- mode:linux -*- */
/**
 * \file open_list.h
 *
 * An open list class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_OPEN_LIST_H_)
#define _OPEN_LIST_H_

#include <queue>

#include "state.h"

using namespace std;

/**
 * A priority queue for states based on their f(s) = g(s) + h(s)
 * value.
 *
 * \todo make this a bit more general.
 */
class OpenList {
public:
	void push(const State *s);
	const State *pop(void);
	bool empty(void) const;

private:
	class OpenListCompare {
	public:
		bool operator()(const State *a, const State *b) const;
	};

	priority_queue<const State *, vector<const State *>, OpenListCompare> pq;
};

#endif	/* !_OPEN_LIST_H_ */
