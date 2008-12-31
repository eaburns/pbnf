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

#include <limits>

#include <queue>

#include "state.h"
#include "open_list.h"

using namespace std;

class CompareOnF {
public:
	bool operator()(State *a, State *b) const {
		float fa = a->get_f();
		float fb = b->get_f();

		if (fa == fb)
			return a->get_g() < b->get_g();

		return fa > fb;
	}

	float get_value(State *s) const {
		return s->get_f();
	}
};


/**
 * A priority queue for states based on their f(s) = g(s) + h(s)
 * value.
 *
 * \todo make this a bit more general.
 */
template<class PQCompare>
class PQOpenList : public OpenList {
public:
	virtual void add(State *s);
	virtual State *take(void);
	virtual State *peek(void);
	virtual bool empty(void);
	virtual void delete_all_states(void);
	virtual float get_best_val(void);
private:
	priority_queue<State *, vector<State *>, PQCompare> pq;
	PQCompare comp;
};

/**
 * Add a state to the OpenList.
 * \param s The state to add.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::add(State *s)
{
	pq.push(s);
	set_best_f(pq.top()->get_f());
}

/**
 * Remove and return the state with the lowest f-value.
 * \return The front of the priority queue.
 */
template<class PQCompare>
State *PQOpenList<PQCompare>::take(void)
{
	State *s;

	s = pq.top();
	pq.pop();

	if (pq.empty())
		set_best_f(numeric_limits<float>::infinity());
	else
		set_best_f(pq.top()->get_f());

	return s;
}

/**
 * Peek at the top element.
 */
template<class PQCompare>
State *PQOpenList<PQCompare>::peek(void)
{
	return pq.top();
}

/**
 * Test if the OpenList is empty.
 * \return True if the open list is empty, false if not.
 */
template<class PQCompare>
bool PQOpenList<PQCompare>::empty(void)
{
	return pq.empty();
}

/**
 * Delete all of the states on the open list.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::delete_all_states(void)
{
	while (!pq.empty()) {
		State *s = pq.top();
		pq.pop();
		delete s;
	}
}

/**
 * Get the value of the best node.
 */
template<class PQCompare>
float PQOpenList<PQCompare>::get_best_val(void)
{
	if (pq.empty())
		return numeric_limits<float>::infinity();

	return comp.get_value(pq.top());
}

#endif	/* !_PQ_OPEN_LIST_H_ */
