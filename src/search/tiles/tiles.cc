/* -*- mode:linux -*- */
/**
 * \file tiles.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#include <assert.h>
#include <math.h>

#include <vector>
#include <iostream>

#include "tiles.h"
#include "tiles_state.h"
#include "../search_domain.h"
#include "../state.h"

using namespace std;

/**
 * Read in a puzzle from the given input stream... this just blindly
 * assumes that it was given a perfect square.
 */
Tiles::Tiles(istream &in)
{
	unsigned int vl;
	unsigned int t_blank = 0, g_blank = 0;
	char buff[1024];
	vector<unsigned int> t;
	vector<unsigned int> g;

	in >> width;
	in >> height;

	in >> buff;
	assert(strcmp(buff, "starting") == 0);
	in >> buff;
	assert(strcmp(buff, "positions") == 0);
	in >> buff;
	assert(strcmp(buff, "for") == 0);
	in >> buff;
	assert(strcmp(buff, "each") == 0);
	in >> buff;
	assert(strcmp(buff, "tile:") == 0);

	for (unsigned int i = 0; i < width * height; i += 1) {
		in >> vl;
		if (vl == 0)
			t_blank = t.size();
		t.push_back(vl);
	}

	in >> buff;
	assert(strcmp(buff, "goal") == 0);
	in >> buff;
	assert(strcmp(buff, "positions:") == 0);

	for (unsigned int i = 0; i < width * height; i += 1) {
		in >> vl;
		if (vl == 0)
			g_blank = g.size();
		g.push_back(vl);
	}

	initial = new TilesState(this, NULL, 0, t, t_blank);
	goal = new TilesState(this, NULL, 0, g, g_blank);
}


/**
 * Create an arbitrary puzzle.  You can't use the starting state of
 * this, it is just really for testing purposes.
 */
Tiles::Tiles(unsigned int width, unsigned int height)
	: width(width), height(height), initial(NULL) {}


/**
 * Destructor.
 */
Tiles::~Tiles(void)
{
	if (initial)
		delete initial;
}


/**
 * Get the initial state.
 *
 * This will be NULL if the puzzle was constructed with the 2-argument
 * width-by-height constructor.
 */
const State *Tiles::initial_state(void)
{
	return initial;
}


/**
 * Get the array for a child with a blank at index 'n' when the
 * parent's blank was at index 'o'.
 */
vector<unsigned int> Tiles::child(vector<unsigned int> tiles,
				  unsigned int o,
				  unsigned int n)
{
	tiles[o] = tiles[n];
	tiles[n] = 0;
	return tiles;
}


/**
 * Expand a state, giving its children.
 */
vector<const State *> *Tiles::expand(const State *s)
{
	const unsigned int cost = 1;
	const TilesState *t = dynamic_cast<const TilesState *>(s);
	vector<const State *> *children = new vector<const State *>;
	vector<unsigned int> tiles = t->get_tiles();
	unsigned int blank = t->get_blank();
	unsigned int col = blank % width;
	unsigned int row = blank / width;


	if (col > 0) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank - 1),
						   blank - 1));
	}
	if (col < width - 1) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank + 1),
						   blank + 1));
	}
	if (row > 0) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank - width),
						   blank - width));
	}
	if (row < height - 1) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank + width),
						   blank + width));
	}

	return children;
}

/**
 * Test if the given state is the goal state.
 */
bool Tiles::is_goal(const State *s) const
{
	return s->equals(goal);
}

/**
 * Print the initial state and goal state.
 */
void Tiles::print(ostream &o) const
{
	cout << "Initial state:" << endl;
	initial->print(o);
	cout << endl << "Goal state:" << endl;
	goal->print(o);
}

unsigned int Tiles::get_width(void) const
{
	return width;
}

unsigned int Tiles::get_height(void) const
{
	return height;
}
