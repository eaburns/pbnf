/* -*- mode:linux -*- */
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
vector<const State *> *AStar::search(const State *init)
{
	vector<const State *> *path = NULL;
	PQOpenList open;
	ClosedList closed;

	open.add(init);

	while (!open.empty() && !path) {
		const State *s = open.take();
		const State *dup = closed.lookup(s);

		if (dup) {
			delete s;
			continue;
		}

		cout << "Expanding:" << endl;
		s->print(cout);
		cout << endl;

		closed.add(s);

		if (s->is_goal()) {
			path = s->get_path();
			cout << "PATH" << endl;
			break;
		}

		vector<const State *> *children = expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			open.add(children->at(i));
			cout << "Generating:" << endl;
			children->at(i)->print(cout);
			cout << endl;

		}
		delete children;
	}

	closed.delete_all_states();
	open.delete_all_states();

	return path;
}
