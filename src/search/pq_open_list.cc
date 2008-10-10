/* -*- mode:linux -*- */
/**
 * \file pq_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

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
	float fa = a->get_g() + a->get_h();
	float fb = b->get_g() + b->get_h();

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

	return s;
}

/**
 * Test if the OpenList is empty.
 * \return True if the open list is empty, false if not.
 */
bool PQOpenList::empty(void)
{
	return pq.empty();
}
