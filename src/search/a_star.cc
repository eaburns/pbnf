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
vector<const State *> *AStar::search(const State *init) const
{
	vector<const State *> *path = NULL;
	OpenList open;
	ClosedList closed;

	open.push(init);
	closed.add(init);

	while (!open.empty()) {
		const State *s = open.pop();

		vector<const State *> *children = s->expand();
		for (unsigned int i = 0; i < children->size(); i += 1) {
			const State *c = children->at(i);

			if (c->is_goal()) {
				State *copy, *last = NULL;
				path = new vector<const State *>;
				while (c) {
					copy = c->clone();
					if (last)
						last->set_parent(copy);
					path->push_back(copy);
					c = c->get_parent();
					last = copy;
				}
				goto out;
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

out:

	closed.delete_all_states();

	return path;
}
