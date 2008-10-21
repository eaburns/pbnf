/* -*- mode:linux -*- */
/**
 * \file queue_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include <queue>

#include "queue_open_list.h"
#include "state.h"

using namespace std;

void QueueOpenList::add(const State *s)
{
	q.push(s);
}

const State *QueueOpenList::take(void)
{
	const State *s = q.front();

	q.pop();

	return s;
}

bool QueueOpenList::empty(void)
{
	return q.empty();
}

void QueueOpenList::delete_all_states(void)
{
	const State *s;

	while (!q.empty()) {
		s = q.front();
		q.pop();
		delete s;
	}
}
