/* -*- mode:linux -*- */
/**
 * \file grid_world.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#if !defined(_GRID_WORLD_H_)
#define _GRID_WORLD_H_

#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "../util/atomic_int.h"

#include "../state.h"
#include "../search_domain.h"
#include "../projection.h"

class GridState;

using namespace std;



class GridWorld : public SearchDomain {
public:
	enum cost_type { UNIT_COST, LIFE_COST };

	GridWorld(istream &s);

	virtual State *initial_state(void);
	virtual vector<const State*> *expand(const State *s);
	virtual void set_projection(Projection *p);
	virtual Projection *get_projection(void) const;

	virtual int get_goal_x(void) const;
	virtual int get_goal_y(void) const;
	virtual int get_width(void) const;
	virtual int get_height(void) const;
	virtual enum cost_type get_cost_type(void) const;
	virtual void print(ostream &o, const vector<const State *> *path) const;
#if defined(ENABLE_IMAGES)
	void export_eps(string file) const;
#endif	/* ENABLE_IMAGES */

	/* The Manhattan Distance heuristic. */
	class ManhattanDist : public Heuristic {
	public:
		ManhattanDist(const SearchDomain *d);
		float compute_up_over(int x, int y,
				      int gx, int gy) const;
		float compute_up_over_down(int x, int y,
					   int gx, int gy) const;
		virtual float compute(const State *s) const;
	};

	/* Projection function that uses the row number mod a value. */
	class RowModProject : public Projection {
	public:
		RowModProject(const SearchDomain *d, unsigned int mod_val);
		virtual ~RowModProject();
		virtual unsigned int project(const State *s);
		virtual unsigned int get_num_nblocks(void);
		virtual vector<unsigned int> get_successors(unsigned int b);
		virtual vector<unsigned int> get_predecessors(unsigned int b);
	private:
		vector<unsigned int> get_neighbors(unsigned int b);
		unsigned int mod_val;
		unsigned int max_row;
	};

private:
	bool on_path(const vector<const State *> *path, int x, int y) const;
	bool is_obstacle(int x, int y) const;

	/* A SearchDomain may have a projection. */
	Projection *project;

	enum cost_type cost_type;

	int width, height;
	int start_x, start_y;
	int goal_x, goal_y;
	map<int, bool> obstacles;

#if defined(ENABLE_IMAGES)
	void expanded_state(const GridState *s);

	AtomicInt expanded;
	vector<AtomicInt> states;
#endif	/* ENABLE_IMAGES */

};

#endif	/* !_GRID_WORLD_H_ */
