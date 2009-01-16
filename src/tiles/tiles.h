/**
 * \file tiles.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#if !defined(_TILES_H_)
#define _TILES_H_

#include <map>
#include <utility>
#include <vector>
#include <iostream>

#include "../search_domain.h"
#include "../state.h"
#include "../projection.h"
#include "../heuristic.h"
#include "tiles_state.h"

using namespace std;

class Tiles : public SearchDomain {
public:
	Tiles(istream &i);
	Tiles(unsigned int width, unsigned int height);
	virtual ~Tiles(void);

	virtual State *initial_state(void);
	virtual vector<State *> *expand(State *s);

	void print(ostream &o) const;
	unsigned int get_width(void) const;
 	unsigned int get_height(void) const;

	class ManhattanDist : public Heuristic {
	public:
		ManhattanDist(const SearchDomain *d);
		virtual ~ManhattanDist(void);
		virtual fp_type compute(State *s) const;
	private:
		void init(const SearchDomain *d);
		fp_type compute_full(TilesState *s) const;
		fp_type compute_incr(TilesState *s,
				   TilesState *p) const;
		int lookup_dist(unsigned int num, unsigned int pos) const;

		unsigned int width;
		unsigned int height;
		vector<unsigned int> table;
	};

	/* only look at 1 tile and the blank. */
	class OneTileProject : public Projection {
	public:
		OneTileProject(const SearchDomain *d);
		virtual ~OneTileProject(void);
		virtual unsigned int project(State *s) const;
		virtual unsigned int get_num_nblocks(void) const;
		virtual vector<unsigned int> get_successors(unsigned int b) const;
		virtual vector<unsigned int> get_predecessors(unsigned int b) const;
		void print(unsigned int b, ostream &o) const;
	private:
		vector<unsigned int> get_neighbors(unsigned int b) const;
		/* 2D vector, the first index is the position of the
		 * blank tile, the second index is the position of
		 * the 1 tile.  The value stored at [i][j] is the
		 * projection ID for the NBlock with the blank at i
		 * and 1 at j. */
		vector<vector<unsigned int> > proj;

		/* Mapping from NBlock IDs to a pair containing the
		 * position of the blank and the position of the 1
		 * tile. */
		vector<pair<unsigned int, unsigned int> > unproj;

		unsigned int nnblocks;

		const Tiles* tiles;
	};

	/* look at the 1-tile, 2-tile and the blank. */
	class TwoTileProject : public Projection {
	public:
		TwoTileProject(const SearchDomain *d);
		virtual ~TwoTileProject(void);
		virtual unsigned int project(State *s) const;
		virtual unsigned int get_num_nblocks(void) const;
		virtual vector<unsigned int> get_successors(unsigned int b) const;
		virtual vector<unsigned int> get_predecessors(unsigned int b) const;
		void print(unsigned int b, ostream &o) const;
	private:
		int setup_proj(unsigned int id,
			       unsigned int i,
			       unsigned int j,
			       unsigned int k);
		vector<unsigned int> get_neighbors(unsigned int b) const;
		/* 3D vector, the first index is the position of the
		 * blank tile, the second index is the position of the
		 * 1 tile, 3rd is the 2-tile.  The value stored at
		 * [i][j][k] is the projection ID for the NBlock with
		 * the blank at i, 1 at j, 2 at k. */
		vector<vector<vector<unsigned int> > > proj;

		/* Mapping from NBlock IDs to a pair containing the
		 * position of the blank and the position of the 1
		 * tile. */
		vector<vector<unsigned int> > unproj;

		unsigned int nnblocks;

		const Tiles* tiles;
	};

	bool is_goal(State *s) const;

	const vector<unsigned int> *get_ones(void) const;
	const vector<uint64_t> *get_fact_ary(void) const;

private:
	vector<unsigned int> child(const vector<unsigned int> *tiles,
				   unsigned int o, unsigned int n);
	unsigned int width;
	unsigned int height;
	vector<unsigned int> initial;
	unsigned int initial_blank;
	TilesState *goal;

	/* Korf's crazy table of the number of ones in the binary
	 * representation on an integer. */
	vector<unsigned int> ones;
	vector<uint64_t> fact_ary;
};

#endif	/* !_TILES_H_ */
