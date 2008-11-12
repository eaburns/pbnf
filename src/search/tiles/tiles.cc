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
#include <stdlib.h>

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
	unsigned int g_blank = 0;
	char buff[1024];
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
			initial_blank = initial.size();
		initial.push_back(vl);
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

	goal = new TilesState(this, NULL, 0, 0, g, g_blank);
	cout << "Goal:" << endl;
	goal->print(cout);
	cout << endl;
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
	if (goal)
		delete goal;
}


/**
 * Get the initial state.
 *
 * This will be NULL if the puzzle was constructed with the 2-argument
 * width-by-height constructor.
 */
const State *Tiles::initial_state(void)
{
	return new TilesState(this, NULL, 0, initial, initial_blank);
}



/**
 * Get the array for a child with a blank at index 'n' when the
 * parent's blank was at index 'o'.
 */
vector<unsigned int> Tiles::child(const vector<unsigned int> *tiles,
				  unsigned int o,
				  unsigned int n)
{
	vector<unsigned int> t = *tiles;
	t[o] = t[n];
	t[n] = 0;
	return t;
}


/**
 * Expand a state, giving its children.
 */
vector<const State *> *Tiles::expand(const State *s)
{
	const unsigned int cost = 1;
	const TilesState *t = dynamic_cast<const TilesState *>(s);
	vector<const State *> *children = new vector<const State *>;
	const vector<unsigned int> *tiles = t->get_tiles();
	unsigned int blank = t->get_blank();
	unsigned int col = blank % width;
	unsigned int row = blank / width;

	const TilesState *gp =
		dynamic_cast<const TilesState *>(s->get_parent());

	if (col > 0 && (!gp || gp->get_blank() != blank -1)) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank - 1),
						   blank - 1));
	}
	if (col < width - 1 && (!gp || gp->get_blank() != blank + 1)) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank + 1),
						   blank + 1));
	}
	if (row > 0 && (!gp || gp->get_blank() != blank - width)) {
		children->push_back(new TilesState(this, s, s->get_g() + cost,
						   child(tiles, blank,
							 blank - width),
						   blank - width));
	}
	if (row < height - 1 && (!gp || gp->get_blank() != blank + width)) {
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
	unsigned int i = 0;

	for (unsigned int y = 0; y < height; y += 1) {
		for (unsigned int x = 0; x < width; x += 1) {
			o << initial[i];
			if (x < width - 1)
				o << "\t";
			i += 1;
		}
		o << endl;
	}

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

void Tiles::ManhattanDist::init(const SearchDomain *d)
{
	const Tiles *t = dynamic_cast<const Tiles*>(d);
	const vector<unsigned int> *goal = t->goal->get_tiles();

	width = t->width;
	height = t->height;

	// build the manhattan distance table.
	table.resize(width * height * width * height);
	for (unsigned int tile = 0; tile < width * height; tile += 1) {
		unsigned int goal_pos;
		for (goal_pos = 0; goal_pos < width * height; goal_pos += 1) {
			if (goal->at(goal_pos) == tile)
				break;
		}
		assert(goal_pos < width * height);
		assert(goal->at(goal_pos) == tile);
		int goal_col = goal_pos % width;
		int goal_row = goal_pos / width;
		for (unsigned int pos = 0; pos < width * height; pos += 1) {
			int col = pos % width;
			int row = pos / width;

			table[(tile * (width * height)) + pos]= abs(goal_col - col)
				+ abs(goal_row - row);
		}
	}
}

Tiles::ManhattanDist::ManhattanDist(const SearchDomain *d)
	: Heuristic(d)
{
	init(d);
}

/**
 * Look up the Manhattan distance of the tile to its goal position in
 * the table.
 */
int Tiles::ManhattanDist::lookup_dist(unsigned int num, unsigned int pos) const
{
	return table[(num * (width * height)) + pos];
}

Tiles::ManhattanDist::~ManhattanDist(void)
{
}

/**
 * Comupte the incremental Manhattan distance of a state.
 */
float Tiles::ManhattanDist::compute(const State *state) const
{
	const TilesState *s = dynamic_cast<const TilesState *>(state);
	const State *p = s->get_parent();

	if (p) {
		const TilesState *ptile =
			dynamic_cast<const TilesState *>(p);
		return comupte_incr(s, ptile);
	}

	return comupte_full(s);
}

/**
 * Comupte the full manhattan distance of the given state.
 */
float Tiles::ManhattanDist::comupte_full(const TilesState *s) const
{
	unsigned int dist = 0;
	const vector<unsigned int> *tiles = s->get_tiles();

	for (unsigned int i = 0; i < tiles->size(); i += 1)
		dist += lookup_dist(tiles->at(i), i);

	return dist;
}

/**
 * Comupte the incremental manhattan distance of the given state using
 * the heuristic value of the parent's state.
 */
float Tiles::ManhattanDist::comupte_incr(const TilesState *s,
					 const TilesState *p) const
{
	unsigned int new_b = s->get_blank();
	unsigned int par_b = p->get_blank();
	unsigned int tile = p->get_tiles()->at(new_b);

	return p->get_h() +  2 * (lookup_dist(tile, par_b)
				  - lookup_dist(tile, new_b));
}
