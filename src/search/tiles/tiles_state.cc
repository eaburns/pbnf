/* -*- mode:linux -*- */
/**
 * \file tiles_state.cc
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

using namespace std;

TilesState::TilesState(SearchDomain *d, const State *parent, float g,
		       float h, vector<unsigned int> tiles,
		       unsigned int blank)
	: State(d, parent, g),
	  tiles(tiles),
	  blank(blank)
{
	this->h = h;
}


TilesState::TilesState(SearchDomain *d, const State *parent, float g,
		       vector<unsigned int> tiles, unsigned int blank)
	: State(d, parent, g),
	  tiles(tiles),
	  blank(blank)
{
	assert(tiles[blank] == 0);
	this->h = domain->get_heuristic()->compute(this);
}


/**
 * Test if the tiles are in order.
 */
bool TilesState::is_goal(void) const
{
	Tiles * t= dynamic_cast<Tiles*>(domain);

	return t->is_goal(this);
}


int TilesState::hash(void) const
{
	int hash = 0;
	unsigned int max_size = tiles.size();

	// sum the place values
	for (unsigned int i = 0; i < max_size; i += 1)
		hash += (int) pow(max_size, i) * tiles[i];

	return hash;
}


State *TilesState::clone(void) const
{
	return new TilesState(domain, parent, g, tiles, blank);
}


void TilesState::print(ostream &o) const
{
	Tiles *t = dynamic_cast<Tiles*>(domain);
	unsigned int i = 0;

	for (unsigned int y = 0; y < t->get_height(); y += 1) {
		for (unsigned int x = 0; x < t->get_width(); x += 1) {
			o << tiles[i];
			if (x < t->get_width() - 1)
				o << "\t";
			i += 1;
		}
		o << endl;
	}
}

/**
 * Test if two states are the same configuration.
 */
bool TilesState::equals(const State *s) const
{
	const TilesState *other = dynamic_cast<const TilesState *>(s);

	for (unsigned int i = 0; i < tiles.size(); i += 1)
		if (tiles[i] != other->tiles[i])
			return false;

	return true;
}

/**
 * Get the tile vector.
 */
vector<unsigned int> TilesState::get_tiles(void) const
{
	return tiles;
}

/**
 * Get the blank position.
 */
unsigned int TilesState::get_blank(void) const
{
	return blank;
}
