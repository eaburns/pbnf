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

#include <vector>
#include <iostream>

#include "tiles.h"
#include "tiles_state.h"
#include "../search_domain.h"
#include "../state.h"

using namespace std;

Tiles::Tiles(istream &i)
{
	assert("unimplemented");
}

Tiles::Tiles(unsigned int width, unsigned int height)
	: width(width), height(height) {}

Tiles::~Tiles(void) {}


State *Tiles::initial_state(void)
{
	assert("unimplemented");
	return NULL;
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
