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
#include <fstream>
#include <map>
#include <string>
#include <vector>

#include <arpa/inet.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../util/eps.h"

#include "grid_state.h"
#include "grid_world.h"

using namespace std;

/**
 * Create a new GridWorld.
 * \param s The istream to read the world file from.
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

	states.resize(width * height, 0UL);

	expanded = 0;
}

/**
 * Get the initial state.
 * \return A new state (that must be deleted by the caller) that
 *         represents the initial state.
 */
State *GridWorld::initial_state(void)
{
	return new GridState(this, NULL, 0, start_x, start_y);
}

/**
 * Expand a gridstate.
 * \param state The state to expand.
 * \return A newly allocated vector of newly allocated children
 *         states.  All of this must be deleted by the caller.
 */
vector<const State*> *GridWorld::expand(const State *state)
{
	const int cost = 1;
	const GridState *s;
	vector<const State*> *children;

	s = dynamic_cast<const GridState*>(state);
	children = new vector<const State*>();

#if defined(ENABLE_IMAGES)
	expanded += 1;
	expanded_state(s);
#endif	// ENABLE_IMAGSE

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

/**
 * Get the x-coordinate of the goal.
 * \return the x-coordinate of the goal.
 */
int GridWorld::get_goal_x(void) const
{
	return goal_x;
}

/**
 * Get the y-coordinate of the goal.
 * \return the y-coordinate of the goal.
 */
int GridWorld::get_goal_y(void) const
{
	return goal_y;
}

/**
 * Get the world width.
 * \return The world width.
 */
int GridWorld::get_width(void) const
{
	return width;
}

/**
 * Get the world height.
 * \return The world height.
 */
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
 * \param o The output stream to print to.
 * \param path An optional parameter that is a vector of states that
 *             form a path in the world.  If given, this path will be displayed.
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
 * \param path The path.
 * \param x The x-coordinate to test.
 * \param y The y-coordinate to test.
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

#if defined(ENABLE_IMAGES)

/**
 * Mark a state as expanded, if this was the first time that the state
 * was expanded, it is marked in the states field so that we can make
 * a display of when each state was expanded.
 * \param s The state that was expanded.
 */
void GridWorld::expanded_state(const GridState *s)
{
	int index = s->get_y() * width + s->get_x();

	// this should be made atomic
	if (states[index] == 0)
		states[index] = expanded;
}

/**
 * Export an image of the order of state expansions to an encapsulated
 * post script file.
 * \param file The name of the file to export to.
 */
void GridWorld::export_eps(string file) const
{
	const int min_size = 500;
	const int max_size = 1000;
	int granularity = expanded < 500 ? 500 / expanded : expanded / 500;
	string data;
	EPS image(width, height);

	if (width < min_size && height < min_size) {
		float min_side = width < height ? width : height;
		image.set_scale(min_size / min_side);
	}

	if (width > max_size || height > max_size) {
		float max_side = width > max_size ? width : height;
		image.set_scale(max_size / max_side);
	}

	// Image red data
	for (int y = height - 1; y >= 0; y -= 1) {
		for (int x = 0; x < width; x += 1) {
			int i = y * width + x;
			char red, green, blue;
			if (is_obstacle(x, y)) {
				// black
				red = green = blue = 0x00;
			} else if (states[i] == 0) {
				// white
				red = green = blue = 0xFF;
			} else {
				// A certain shade of orange
				int number = states[i];
				int x = expanded < 500 ? number * granularity
					: number / granularity;
				if (x < 125) {
					red = 255;
					green = 255;
					blue = 125 - x;
				} else if (x < 380) {
					red = 255;
					green = 255 - (x - 125);
					blue = 0;
				} else {
					red = 255 - (x - 380);
					green = blue = 0;
				}

			}
			data += red;
			data += green;
			data += blue;
		}
	}

	image.set_data(data);
	image.output(file);
}

#endif	// ENABLE_IMAGES
