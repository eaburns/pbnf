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
#include "open_list.h"
#include "closed_list.h"
#include "a_star.h"

/**
 * Perform an A* search.
 */
vector<const State *> *AStar::search(const State *init)
{
	vector<const State *> *path = NULL;
	OpenList open;
	ClosedList closed;

	open.push(init);
	closed.add(init);

	while (!open.empty() && !path) {
		const State *s = open.pop();

		vector<const State *> *children = expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			const State *c = children->at(i);
			if (c->is_goal()) {
				path = c->get_path();
				for (; i < children->size(); i += 1)
					delete children->at(i);
				break;
			}
			if (closed.lookup(c) != NULL) {
				delete c;
				continue;
			}
			closed.add(c);
			open.push(c);
		}
		delete children;
	}

	closed.delete_all_states();

	return path;
}
