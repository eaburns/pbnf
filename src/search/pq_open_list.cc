/* -*- mode:linux -*- */
/**
 * \file pq_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <math.h>

#include <queue>

#include "state.h"
#include "pq_open_list.h"
#include "open_list.h"

using namespace std;

/**
 * Compares states by their f values.  Tie-breaking is based on g values.
 */
bool PQOpenList::PQCompare::operator()(const State *a,
				       const State *b) const
{
	float fa = a->get_f();
	float fb = b->get_f();

	if (fa == fb)
		return a->get_g() < b->get_g();

	return fa > fb;
}

/**
 * Add a state to the OpenList.
 * \param s The state to add.
 */
void PQOpenList::add(const State *s)
{
	pq.push(s);
	set_best_f(pq.top()->get_f());
}

/**
 * Remove and return the state with the lowest f-value.
 * \return The front of the priority queue.
 */
const State *PQOpenList::take(void)
{
	const State *s;

	s = pq.top();
	pq.pop();

	if (pq.empty())
		set_best_f(INFINITY);
	else
		set_best_f(pq.top()->get_f());

	return s;
}

/**
 * Peek at the top element.
 */
const State *PQOpenList::peek(void)
{
	return pq.top();
}

/**
 * Test if the OpenList is empty.
 * \return True if the open list is empty, false if not.
 */
bool PQOpenList::empty(void)
{
	return pq.empty();
}

/**
 * Delete all of the states on the open list.
 */
void PQOpenList::delete_all_states(void)
{
	while (!pq.empty()) {
		const State *s = pq.top();
		pq.pop();
		delete s;
	}
}
