/* -*- mode:linux -*- */
/**
 * \file closed_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <map>

#include "state.h"
#include "closed_list.h"

void ClosedList::add(const State *s)
{
	m[s->hash()] = s;
}

const State *ClosedList::lookup(int hash) const
{
	// this is stupid: apparently you can't do an assignment with
	// iterators, so instead we need to do two lookups.

	if (m.find(hash) == m.end())
		return NULL;

	return m.find(hash)->second;
}
