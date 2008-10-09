/* -*- mode:linux -*- */
/**
 * \file open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <queue>

#include "state.h"
#include "open_list.h"

using namespace std;

/**
 * Compares states by their f values.
 */
bool OpenList::OpenListCompare::operator()(const State *a, const State *b) const
{
	float fa = a->get_g() + a->get_h();
	float fb = b->get_g() + b->get_h();

	if (fa == fb)
		return a->get_g() < b->get_g();

	return fa > fb;
}

void OpenList::push(const State *s)
{
	pq.push(s);
}

const State *OpenList::pop(void)
{
	const State *s;

	s = pq.top();
	pq.pop();

	return s;
}

bool OpenList::empty(void) const
{
	return pq.empty();
}
