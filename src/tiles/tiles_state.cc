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

void TilesState::compute_hash(void)
{
	unsigned int bits = 0;
	const Tiles *t = dynamic_cast<const Tiles *>(domain);
	const vector<unsigned int> *ones = t->get_ones();
	const vector<uint64_t> *fact_ary = t->get_fact_ary();

	hash_val = 0;
	for (int i = tiles.size() - 1; i >= 0; i -= 1) {
		unsigned int k = tiles[i];
		unsigned int mask = ~((~0) << k);
		unsigned int v = mask & bits;
		unsigned int d = k - ones->at(v);
		hash_val += d * fact_ary->at(i);
		bits |= 1 << k;
	}
}


TilesState::TilesState(SearchDomain *d, State *parent, fp_type g,
		       fp_type h_val, vector<unsigned int> tiles,
		       unsigned int blank)
	: State(d, parent, g),
	  tiles(tiles),
	  blank(blank)
{
	this->h = h_val;
	compute_hash();
}


TilesState::TilesState(SearchDomain *d, State *parent, fp_type g,
		       vector<unsigned int> t, unsigned int b)
	: State(d, parent, g),
	  tiles(t),
	  blank(b)
{
	assert(t[b] == 0);
	this->h = domain->get_heuristic()->compute(this);
	assert(this->h == 0 ? is_goal() : 1);
	compute_hash();
}


/**
 * Test if the tiles are in order.
 */
bool TilesState::is_goal(void)
{
	Tiles * t= dynamic_cast<Tiles*>(domain);

	return t->is_goal(this);
}


uint64_t TilesState::hash(void) const
{
	return hash_val;
}


State *TilesState::clone(void) const
{
	return new TilesState(domain, parent, g, tiles, blank);
}


void TilesState::print(ostream &o) const
{
	Tiles *t = dynamic_cast<Tiles*>(domain);
	unsigned int i = 0;

	o << "Hash: " << hash_val << endl;
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
bool TilesState::equals(State *s) const
{
	TilesState *other = dynamic_cast<TilesState *>(s);

	for (unsigned int i = 0; i < tiles.size(); i += 1)
		if (tiles[i] != other->tiles[i])
			return false;

	return true;
}

/**
 * Get the tile vector.
 */
const vector<unsigned int> *TilesState::get_tiles(void) const
{
	return &tiles;
}

/**
 * Get the blank position.
 */
unsigned int TilesState::get_blank(void) const
{
	return blank;
}
