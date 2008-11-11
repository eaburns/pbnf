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
		unsigned int get_goal_dist(const Tiles *d,
					   int col,
					   int row,
					   unsigned int num) const;

		float comupte_full(const TilesState *s) const;
		float comupte_incr(const TilesState *s,
				   const TilesState *p) const;
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

private:
	vector<unsigned int> child(vector<unsigned int> tiles,
				   unsigned int o, unsigned int n);
	unsigned int width;
	unsigned int height;
	vector<unsigned int> initial;
	unsigned int initial_blank;
	const TilesState *goal;
};

#endif	/* !_TILES_H_ */
