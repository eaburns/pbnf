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

#include <assert.h>

#include <limits>
#include <algorithm>

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
	PQOpenList(void);
	void add(State *s);
	State *take(void);
	State *peek(void);
	bool empty(void);
	void delete_all_states(void);
	float get_best_val(void);
	void prune(void);

	void resort(State *s);
private:
	vector<State *> heap;
	PQCompare comp;
};

/**
 * Create a new PQ open list.
 */
template<class PQCompare>
PQOpenList<PQCompare>::PQOpenList(void)
{
	make_heap(heap.begin(), heap.end(), comp);
}

/**
 * Add a state to the OpenList.
 * \param s The state to add.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::add(State *s)
{
	s->set_open(true);
	heap.push_back(s);
	push_heap(heap.begin(), heap.end(), comp);
	set_best_f(heap.front()->get_f());
}

/**
 * Remove and return the state with the lowest f-value.
 * \return The front of the priority queue.
 */
template<class PQCompare>
State *PQOpenList<PQCompare>::take(void)
{
	State *s;

	s = heap.front();
	s->set_open(false);
	pop_heap(heap.begin(), heap.end(), comp);
	heap.pop_back();

	if (heap.empty())
		set_best_f(numeric_limits<float>::infinity());
	else
		set_best_f(heap.front()->get_f());

	return s;
}

/**
 * Peek at the top element.
 */
template<class PQCompare>
State *PQOpenList<PQCompare>::peek(void)
{
	return heap.front();
}

/**
 * Test if the OpenList is empty.
 * \return True if the open list is empty, false if not.
 */
template<class PQCompare>
bool PQOpenList<PQCompare>::empty(void)
{
	return heap.empty();
}

/**
 * Delete all of the states on the open list.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::delete_all_states(void)
{
	vector<State *>::iterator iter;

	for (iter = heap.begin(); iter != heap.end(); iter++)
		delete *iter;

	heap.clear();
}

/**
 * Prune all of the states.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::prune(void)
{
	vector<State *>::iterator iter;

	for (iter = heap.begin(); iter != heap.end(); iter++)
		(*iter)->set_open(false);

	heap.clear();
}

/**
 * Get the value of the best node.
 */
template<class PQCompare>
float PQOpenList<PQCompare>::get_best_val(void)
{
	if (heap.empty())
		return numeric_limits<float>::infinity();

	return comp.get_value(heap.front());
}

/**
 * Ensure that the heap propert holds.  This should be called after
 * updating states which are open.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::resort(State *s)
{
	vector<State *>::iterator iter;

	for (iter = heap.begin(); iter != heap.end(); iter++)
		if (*iter == s) {
			push_heap(heap.begin(), ++iter, comp);
			return;
		}

	assert("should not reach here" == NULL);
}

#endif	/* !_PQ_OPEN_LIST_H_ */
