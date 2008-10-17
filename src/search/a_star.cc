/* -*- mode:linux -*- */
/**
 * \file a_star.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include "state.h"
#include "pq_open_list.h"
#include "closed_list.h"
#include "a_star.h"

/**
 * Perform an A* search.
 */
vector<const State *> *AStar::search(const State *init)
{
	vector<const State *> *path = NULL;
	PQOpenList open;
	ClosedList closed;

	open.add(init);
	closed.add(init);

	while (!open.empty() && !path) {
		const State *s = open.take();

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		vector<const State *> *children = expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			const State *c = children->at(i);
			if (closed.lookup(c) != NULL) {
				delete c;
				continue;
			}
			closed.add(c);
			open.add(c);
		}
		delete children;
	}

	closed.delete_all_states();

	return path;
}
