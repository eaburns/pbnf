/* -*- mode:linux -*- */
/**
 * \file queue_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include <math.h>

#include <queue>

#include "queue_open_list.h"
#include "state.h"

using namespace std;

void QueueOpenList::add(const State *s)
{
	q.push(s);
	set_best_f(q.front()->get_f());
}

const State *QueueOpenList::take(void)
{
	const State *s = q.front();

	q.pop();
	if (q.empty())
		set_best_f(INFINITY);
	else
		set_best_f(q.front()->get_f());


	return s;
}

const State *QueueOpenList::peek(void)
{
	return q.front();
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
