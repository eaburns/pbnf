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

#include "state.h"
#include "open_list.h"
#include "util/priority_queue.h"

using namespace std;

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
	fp_type get_best_val(void);
	void prune(void);
	unsigned int size(void);

	void resort(State *s);
private:
	PriorityQueue<State *, PQCompare, PQCompare> pq;
	PQCompare get_index;
	PQCompare comp;
};

/**
 * Create a new PQ open list.
 */
template<class PQCompare>
	PQOpenList<PQCompare>::PQOpenList(void)
{
}

/**
 * Add a state to the OpenList.
 * \param s The state to add.
 */
template<class PQCompare>
void PQOpenList<PQCompare>::add(State *s)
{
	s->set_open(true);
	pq.add(s);
}

/**
 * Remove and return the state with the lowest f-value.
 * \return The front of the priority queue.
 */
template<class PQCompare>
State *PQOpenList<PQCompare>::take(void)
{
	State *s;

	s = pq.take();
	s->set_open(false);

	if (pq.empty())
		set_best_f(fp_infinity);
	else
		set_best_f(pq.peek()->get_f());

	return s;
}

/**
 * Peek at the top element.
 */
template<class PQCompare>
 State * PQOpenList<PQCompare>::peek(void)
{
	return pq.peek();
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
	while (!pq.empty())
		delete pq.take();

	pq.reset();
}

/**
 * Prune all of the states.
 */
template<class PQCompare>
 void PQOpenList<PQCompare>::prune(void)
{
	int fill = pq.get_fill();

	for (int i = 0; i < fill; i += 1)
		pq.get_elem(i)->set_open(false);

	pq.reset();
}

template<class PQCompare>
 unsigned int PQOpenList<PQCompare>::size(void)
{
	return pq.get_size();
}

/**
 * Get the value of the best node.
 */
template<class PQCompare>
 fp_type PQOpenList<PQCompare>::get_best_val(void)
{
	if (pq.empty())
		return fp_infinity;

	return comp.get_value(pq.peek());
}

/**
 * Ensure that the heap propert holds.  This should be called after
 * updating states which are open.
 */
template<class PQCompare>
	void PQOpenList<PQCompare>::resort(State *s)
{
	pq.elem_improved(get_index(s));
}

#endif	/* !_PQ_OPEN_LIST_H_ */
