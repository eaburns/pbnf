/* -*- mode:linux -*- */
/**
 * \file pq_open_list.h
 *
 * An open list class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_PQ_OPEN_LIST_H_)
#define _PQ_OPEN_LIST_H_

#include <queue>

#include "state.h"
#include "open_list.h"

using namespace std;

/**
 * A priority queue for states based on their f(s) = g(s) + h(s)
 * value.
 *
 * \todo make this a bit more general.
 */
class PQOpenList : public OpenList {
public:
	virtual void add(const State *s);
	virtual const State *take(void);
	virtual bool empty(void);

private:
	class PQCompare {
	public:
		bool operator()(const State *a, const State *b) const;
	};

	priority_queue<const State *, vector<const State *>, PQCompare> pq;
};

#endif	/* !_PQ_OPEN_LIST_H_ */
