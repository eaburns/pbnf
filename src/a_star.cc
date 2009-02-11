/**
 * \file a_star.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <assert.h>

#include "state.h"
#include "pq_open_list.h"
#include "closed_list.h"
#include "a_star.h"

AStar::~AStar(void) {}

/**
 * Perform an A* search.
 */
vector<State *> *AStar::search(State *init)
{
	vector<State *> *path = NULL;
	PQOpenList<State::CompareOnF> open;
	ClosedList closed;

	open.add(init);

	while (!open.empty() && !path) {
		State *s = open.take();

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		vector<State *> *children = expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			State *c = children->at(i);
			State *dup = closed.lookup(c);
			if (dup) {
				if (dup->get_g() > c->get_g()) {
					dup->update(c->get_parent(), c->get_g());
					if (dup->is_open())
						open.resort(dup);
					else
						open.add(dup);
				}
				delete c;
			} else {
				open.add(c);
				closed.add(c);
			}

		}
		delete children;
	}

	closed.delete_all_states();

	return path;
}
