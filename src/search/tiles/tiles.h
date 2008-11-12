/* -*- mode:linux -*- */
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

#include "../search_domain.h"
#include "../state.h"
#include "../projection.h"
#include "../heuristic.h"
#include "tiles_state.h"

class Tiles : public SearchDomain {
public:
	Tiles(istream &i);
	Tiles(unsigned int width, unsigned int height);
	virtual ~Tiles(void);

	virtual const State *initial_state(void);
	virtual vector<const State *> *expand(const State *s);

	void print(ostream &o) const;
	unsigned int get_width(void) const;
 	unsigned int get_height(void) const;

	class ManhattanDist : public Heuristic {
	public:
		ManhattanDist(const SearchDomain *d);
		virtual ~ManhattanDist(void);
		virtual float compute(const State *s) const;
	private:
		void init(const SearchDomain *d);
		float compute_full(const TilesState *s) const;
		float compute_incr(const TilesState *s,
				   const TilesState *p) const;
		int lookup_dist(unsigned int num, unsigned int pos) const;

		unsigned int width;
		unsigned int height;
		vector<unsigned int> table;
	};

/*
	class BlankTilesProject : public Projection {
	public:
		BlankTilesProject(const SearchDomain *d, unsigned int blanks);
		virtual ~BlankTilesProject(void);
		virtual unsigned int project(const State *s) const;
		virtual unsigned int get_num_nblocks(void) const;
		virtual vector<unsigned int> get_successors(unsigned int b) const;
		virtual vector<unsigned int> get_predecessors(unsigned int b) const;
	};
*/

	bool is_goal(const State *s) const;

	const vector<unsigned int> *get_ones(void) const;

private:
	vector<unsigned int> child(const vector<unsigned int> *tiles,
				   unsigned int o, unsigned int n);
	unsigned int width;
	unsigned int height;
	vector<unsigned int> initial;
	unsigned int initial_blank;
	const TilesState *goal;

	/* Korf's crazy table of the number of ones in the binary
	 * representation on an integer. */
	vector<unsigned int> ones;
};

#endif	/* !_TILES_H_ */
