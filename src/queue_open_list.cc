/**
 * \file queue_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include <limits>
#include <queue>

#include "queue_open_list.h"
#include "state.h"

using namespace std;

void QueueOpenList::add(State *s)
{
	s->set_open(true);
	q.push(s);
	set_best_f(q.front()->get_f());
}

State *QueueOpenList::take(void)
{
	State *s = q.front();

	s->set_open(false);
	q.pop();
	if (q.empty())
		set_best_f(numeric_limits<float>::infinity());
	else
		set_best_f(q.front()->get_f());


	return s;
}

State *QueueOpenList::peek(void)
{
	return q.front();
}

bool QueueOpenList::empty(void)
{
	return q.empty();
}

void QueueOpenList::delete_all_states(void)
{
	State *s;

	while (!q.empty()) {
		s = q.front();
		q.pop();
		delete s;
	}
}

void QueueOpenList::prune(void)
{
	while (!q.empty())
		q.pop();
}
