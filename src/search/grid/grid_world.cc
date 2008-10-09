/* -*- mode:linux -*- */
/**
 * \file grid_world.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <iostream>
#include <map>
#include <vector>

#include <stdlib.h>
#include <string.h>

#include "grid_state.h"
#include "grid_world.h"

using namespace std;

/**
 * Create a new GridWorld.
 */
GridWorld::GridWorld(istream &s)
{
	char line[100];
	char c;

	s >> height;
	s >> width;

	s >> line;
	if(strcmp(line, "Board:") != 0) {
		cerr << "Parse error: expected \"Board:\"" << endl;
		exit(EXIT_FAILURE);
	}
	c = s.get();		// new-line
	if (c != '\n') {
		cerr << endl << "Parse error: [" << c << "]" << endl;
		exit(EXIT_FAILURE);
	}
	for (int h = 0; h < height; h += 1) {
		for (int w = 0; w < width; w += 1) {
			c = s.get();
			if (c == '#')
				obstacles[width * h + w] = true;
		}
		c = s.get();	// new-line
		if (c != '\n') {
			cerr << endl << "Parse error: [" << c << "]" << endl;
			exit(EXIT_FAILURE);
		}
	}

	// Cost (Unit/Life)
	s >> line;
	// Movement (Four-way/Eight-way)
	s >> line;

	s >> start_x;
	s >> start_y;
	s >> goal_x;
	s >> goal_y;
}

/**
 * Get the initial state.
 */
State *GridWorld::initial_state(void)
{
	return new GridState(this, NULL, 0, start_x, start_y);
}

/**
 * Expand a gridstate.
 */
vector<const State*> *GridWorld::expand(const State *state) const
{
	const int cost = 1;
	const GridState *s;
	vector<const State*> *children;

	s = dynamic_cast<const GridState*>(state);
	children = new vector<const State*>();

	if (s->get_x() > 0 && !is_obstacle(s->get_x() - 1, s->get_y())) {
		children->push_back(new GridState(this, state, s->get_g() + cost,
						  s->get_x() - 1, s->get_y()));
	}
	if (s->get_x() < width - 1 && !is_obstacle(s->get_x() + 1, s->get_y())) {
		children->push_back(new GridState(this, state, s->get_g() + cost,
						  s->get_x() + 1, s->get_y()));
	}
	if (s->get_y() > 0 && !is_obstacle(s->get_x(), s->get_y() - 1)) {
			children->push_back(new GridState(this, state, s->get_g() + cost,
						  s->get_x(), s->get_y() - 1));
	}
	if (s->get_y() < height - 1 && !is_obstacle(s->get_x(), s->get_y() + 1)) {
		children->push_back(new GridState(this, state, s->get_g() + cost,
						  s->get_x(), s->get_y() + 1));
	}

	return children;
}

int GridWorld::get_goal_x(void) const
{
	return goal_x;
}

int GridWorld::get_goal_y(void) const
{
	return goal_y;
}

int GridWorld::get_width(void) const
{
	return width;
}

int GridWorld::get_height(void) const
{
	return height;
}

/**
 * Test if there is an obstacle at the given location.
 */
bool GridWorld::is_obstacle(int x, int y) const
{
	map<int, bool>::const_iterator iter;

	iter = obstacles.find(width * y + x);

	return iter != obstacles.end();
}

/**
 * Prints the grid world to the given stream.
 */
void GridWorld::print(ostream &o, const vector<const State *> *path = NULL) const
{
	o << height << " " << width << endl;
	o << "Board:" << endl;

	for (int h = 0; h < height; h += 1) {
		for (int w = 0; w < width; w += 1) {
			if (is_obstacle(w, h))
				o << "#";
			else if (path && on_path(path, w, h))
				o << "o";
			else
				o << " ";
		}
		o << endl;;
	}

	o << "Unit" << endl;
	o << "Four-way" << endl;
	o << start_x << " " << start_y << "\t" << goal_x << " " << goal_y << endl;
}

/**
 * Test whether or not a location is on the given path.
 */
bool GridWorld::on_path(const vector<const State *> *path, int x, int y) const
{
	if (!path)
		return false;

	for (unsigned int i = 0; i < path->size(); i += 1) {
		const GridState *s = dynamic_cast<const GridState *>(path->at(i));
		if (s->get_x() == x && s->get_y() == y)
			return true;
	}

	return false;
}
