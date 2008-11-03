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

#include "tiles_state.h"

using namespace std;

TilesState::TilesState(SearchDomain *d, const State *parent, float g,
		       vector<unsigned int> tiles, unsigned int blank)
	: State(d, parent, g),
	  tiles(tiles),
	  blank(blank)
{
	assert(tiles[blank] == 0);
}


/**
 * Test if the tiles are in order.
 */
bool TilesState::is_goal(void) const
{
	for (unsigned int i = 0; i < tiles.size(); i += 1) {
		if (tiles[i] != i)
			return false;
	}

	return true;
}


int TilesState::hash(void) const
{
	int hash = 0;
	unsigned int max_size = tiles.size();

	// sum the place values
	for (unsigned int i = 0; i < max_size; i += 1)
		hash += pow(max_size, i) * tiles[i];

	return hash;
}


State *TilesState::clone(void) const
{
	return new TilesState(domain, parent, g, tiles, blank);
}


void TilesState::print(ostream &o) const
{
	vector<unsigned int>::const_iterator iter;

	for (iter = tiles.begin(); iter != tiles.end(); iter++)
		o << *iter << " ";

	o << endl;
}


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

unsigned int TilesState::get_blank(void) const
{
	return blank;
}
