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
#include <string.h>

#include <vector>
#include <iostream>
#include <map>
#include <utility>

#include "tiles.h"
#include "tiles_state.h"
#include "../search_domain.h"
#include "../state.h"

using namespace std;

/**
 * Read in a puzzle from the given input stream...
 *
 * The datafiles list the position for each corresponding tile.  This
 * means that the first number read is the initial state's position of
 * the 0th tile (the blank).  The next number read is the position of
 * the 1 tile, etc.
 */
Tiles::Tiles(istream &in)
{
	unsigned int pos;
	unsigned int g_blank = 0;
	char buff[1024];
	vector<unsigned int> g;
	uint64_t pow;

	in >> height;
	in >> width;

/*
	cout << "height = " << height << endl;
	cout << "width = " << width << endl;
*/

	assert((width * height - 1) <= (sizeof(pow) * 8));
	// 2^(w*h-1)
	pow = ((uint64_t) 1) << (width * height - 1);

	ones.resize(pow + 1);
	for (unsigned int i = 1; i <= pow; i += 1) {
		uint64_t bits = 0;
		uint64_t j = i;

		while (j) {
			bits += j & 0x1;
			j >>= 1;
		}
		ones[i] = bits;
	}

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

	initial.resize(width * height);
	for (unsigned int i = 0; i < width * height; i += 1) {
		in >> pos;
		if (i == 0)
			initial_blank = pos;
		initial[pos] = i;
	}

	in >> buff;
	assert(strcmp(buff, "goal") == 0);
	in >> buff;
	assert(strcmp(buff, "positions:") == 0);

	g.resize(width * height);
	for (unsigned int i = 0; i < width * height; i += 1) {
		in >> pos;
		if (i == 0)
			g_blank = pos;
		g[pos] = i;
	}

	/* precompute factorials. */
	fact_ary.resize((width * height) + 1);
	fact_ary[0] = 1;
	for (unsigned int i = 1; i < (width * height) + 1; i += 1)
		fact_ary[i] = fact_ary[i - 1] * i;

	goal = new TilesState(this, NULL, 0, 0, g, g_blank);
}

const vector<uint64_t> *Tiles::get_ones() const
{
	return &ones;
}

const vector<uint64_t> *Tiles::get_fact_ary() const
{
	return &fact_ary;
}


/**
 * Create an arbitrary puzzle.  You can't use the starting state of
 * this, it is just really for testing purposes.
 */
Tiles::Tiles(unsigned int width, unsigned int height)
	: width(width), height(height) {}


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
State *Tiles::initial_state(void)
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
vector<State *> *Tiles::expand(State *s)
{
	const unsigned int cost = fp_one;
	TilesState *t = dynamic_cast<TilesState *>(s);
	vector<State *> *children = new vector<State *>;
	const vector<unsigned int> *tiles = t->get_tiles();
	unsigned int blank = t->get_blank();
	unsigned int col = blank % width;
	unsigned int row = blank / width;

	TilesState *gp =
		dynamic_cast<TilesState *>(s->get_parent());

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
bool Tiles::is_goal(State *s) const
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

/**********************************************************************/

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

			table[(tile * (width * height)) + pos] =
				(abs(goal_col - col) + abs(goal_row - row)) * fp_one;
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
 * Compute the incremental Manhattan distance of a state.
 */
fp_type Tiles::ManhattanDist::compute(State *state) const
{
	fp_type ret = 0;
	TilesState *s = dynamic_cast<TilesState *>(state);
	State *p = s->get_parent();

	if (p) {
		TilesState *ptile =
			dynamic_cast<TilesState *>(p);
		ret = compute_incr(s, ptile);
//		assert(ret == compute_full(s));
	} else
		ret = compute_full(s);

	assert(ret >= 0);

	return ret;
}

/**
 * Compute the full manhattan distance of the given state.
 */
fp_type Tiles::ManhattanDist::compute_full(TilesState *s) const
{
	unsigned int dist = 0;
	const vector<unsigned int> *tiles = s->get_tiles();

	for (unsigned int i = 0; i < tiles->size(); i += 1)
		if (tiles->at(i) != 0)
			dist += lookup_dist(tiles->at(i), i);

	return dist;
}

/**
 * Compute the incremental manhattan distance of the given state using
 * the heuristic value of the parent's state.
 */
fp_type Tiles::ManhattanDist::compute_incr(TilesState *s,
					 TilesState *p) const
{
	unsigned int new_b = s->get_blank();
	unsigned int par_b = p->get_blank();
	unsigned int tile = p->get_tiles()->at(new_b);
	fp_type ret = 0;

	ret = p->get_h() + (lookup_dist(tile, par_b)
			    - lookup_dist(tile, new_b));
	assert(ret >= 0);
	return ret;
}

/**********************************************************************/

Tiles::OneTileProject::OneTileProject(const SearchDomain *d)
{
	tiles = dynamic_cast<const Tiles *>(d);
	unsigned int size = tiles->width * tiles->height;
	unsigned int id = 0;

	nnblocks = size * (size - 1);

	unproj.resize(nnblocks);
	proj.resize(size);
	for (unsigned int i = 0; i < size; i += 1) {
		proj[i].resize(size);
		for (unsigned int j = 0; j < size; j += 1) {
			if (i == j)
				continue;

			proj[i][j] = id;
//			cout << "proj[" << i << "][" << j << "]=" << id << endl;
			unproj[id] = pair<unsigned int, unsigned int>(i, j);
			id += 1;
		}
	}
}

Tiles::OneTileProject::~OneTileProject(void)
{
	// nothing
}

unsigned int Tiles::OneTileProject::project(State *s) const
{
	TilesState *ts = dynamic_cast<TilesState *>(s);
	const vector<unsigned int> *t = ts->get_tiles();
	unsigned int size = t->size();
	unsigned int blank = 0;
	unsigned int one = 0;

	for (unsigned int i = 0; i < size; i += 1) {
		if (t->at(i) == 0)
			blank = i;
		else if (t->at(i) == 1)
			one = i;
	}

	assert(blank != one);

	return proj[blank][one];
}

unsigned int Tiles::OneTileProject::get_num_nblocks(void) const
{
	return nnblocks;
}

vector<unsigned int> Tiles::OneTileProject::get_neighbors(unsigned int b) const
{
	vector<unsigned int> ret;
	unsigned int blank = unproj[b].first;
	unsigned int one = unproj[b].second;
	unsigned int width = tiles->width;
	unsigned int col = blank % width;
	unsigned int row = blank / width;

	if (col > 0) {
		unsigned int i = blank - 1;
		if (one == i)
			ret.push_back(proj[one][blank]);
		else
			ret.push_back(proj[i][one]);
	}
	if (col < width - 1) {
		unsigned int i = blank + 1;
		if (one == i)
			ret.push_back(proj[one][blank]);
		else
			ret.push_back(proj[i][one]);
	}
	if (row > 0) {
		unsigned int i = blank - width;
		if (one == i)
			ret.push_back(proj[one][blank]);
		else
			ret.push_back(proj[i][one]);
	}
	if (row < tiles->height - 1) {
		unsigned int i = blank + width;
		if (one == i)
			ret.push_back(proj[one][blank]);
		else
			ret.push_back(proj[i][one]);
	}

	return ret;
}

vector<unsigned int> Tiles::OneTileProject::get_successors(unsigned int b) const
{
	return get_neighbors(b);
}

vector<unsigned int> Tiles::OneTileProject::get_predecessors(unsigned int b) const
{
	return get_neighbors(b);
}

/**
 * Print the projection with the given ID, b.
 */
void Tiles::OneTileProject::print(unsigned int b, ostream &o) const
{
	o << b << ": "
	  << "blank=" << unproj[b].first
	  << ", one=" << unproj[b].second
	  << endl;
}

/**********************************************************************/

int Tiles::TwoTileProject::setup_proj(unsigned int id,
				      unsigned int i,
				      unsigned int j,
				      unsigned int k)
{
	if (i == j || i == k || j == k)
		return 0;

	proj[i][j][k] = id;
	unproj[id].resize(3);
	unproj[id][0] = i;
	unproj[id][1] = j;
	unproj[id][2] = k;

	return 1;
}

Tiles::TwoTileProject::TwoTileProject(const SearchDomain *d)
{
	tiles = dynamic_cast<const Tiles *>(d);
	unsigned int size = tiles->width * tiles->height;
	unsigned int id = 0;

	nnblocks = size * (size - 1) * (size - 2);

	unproj.resize(nnblocks);
	proj.resize(size);
	for (unsigned int i = 0; i < size; i += 1) {
		proj[i].resize(size);
		for (unsigned int j = 0; j < size; j += 1) {
			proj[i][j].resize(size);
			for (unsigned int k = 0; k < size; k += 1)
				id += setup_proj(id, i, j, k);
		}
	}
}

Tiles::TwoTileProject::~TwoTileProject(void)
{
	// nothing
}

unsigned int Tiles::TwoTileProject::project(State *s) const
{
	TilesState *ts = dynamic_cast<TilesState *>(s);
	const vector<unsigned int> *t = ts->get_tiles();
	unsigned int size = t->size();
	unsigned int blank = 0;
	unsigned int one = 0;
	unsigned int two = 0;

	for (unsigned int i = 0; i < size; i += 1) {
		if (t->at(i) == 0)
			blank = i;
		else if (t->at(i) == 1)
			one = i;
		else if (t->at(i) == 2)
			two = i;
	}

	assert(blank != one);
	assert(blank != two);
	assert(one != two);

	return proj[blank][one][two];
}

unsigned int Tiles::TwoTileProject::get_num_nblocks(void) const
{
	return nnblocks;
}

vector<unsigned int> Tiles::TwoTileProject::get_neighbors(unsigned int b) const
{
	vector<unsigned int> ret;
	unsigned int blank = unproj[b][0];
	unsigned int one = unproj[b][1];
	unsigned int two = unproj[b][2];
	unsigned int width = tiles->width;
	unsigned int col = blank % width;
	unsigned int row = blank / width;

	if (col > 0) {
		unsigned int i = blank - 1;
		if (one == i)
			ret.push_back(proj[one][blank][two]);
		else if (two == i)
			ret.push_back(proj[two][one][blank]);
		else
			ret.push_back(proj[i][one][two]);
	}
	if (col < width - 1) {
		unsigned int i = blank + 1;
		if (one == i)
			ret.push_back(proj[one][blank][two]);
		else if (two == i)
			ret.push_back(proj[two][one][blank]);
		else
			ret.push_back(proj[i][one][two]);
	}
	if (row > 0) {
		unsigned int i = blank - width;
		if (one == i)
			ret.push_back(proj[one][blank][two]);
		else if (two == i)
			ret.push_back(proj[two][one][blank]);
		else
			ret.push_back(proj[i][one][two]);
	}
	if (row < tiles->height - 1) {
		unsigned int i = blank + width;
		if (one == i)
			ret.push_back(proj[one][blank][two]);
		else if (two == i)
			ret.push_back(proj[two][one][blank]);
		else
			ret.push_back(proj[i][one][two]);
	}

	return ret;
}

vector<unsigned int> Tiles::TwoTileProject::get_successors(unsigned int b) const
{
	return get_neighbors(b);
}

vector<unsigned int> Tiles::TwoTileProject::get_predecessors(unsigned int b) const
{
	return get_neighbors(b);
}

/**
 * Print the projection with the given ID, b.
 */
void Tiles::TwoTileProject::print(unsigned int b, ostream &o) const
{
	o << b << ": "
	  << "blank=" << unproj[b][0]
	  << ", one=" << unproj[b][1]
	  << ", two=" << unproj[b][2]
	  << endl;
}
