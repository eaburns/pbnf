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

class GridState;

using namespace std;

class GridWorld : public SearchDomain {
public:
	GridWorld(istream &s);

	virtual State *initial_state(void);
	virtual vector<const State*> *expand(const State *s);

	virtual int get_goal_x(void) const;
	virtual int get_goal_y(void) const;
	virtual int get_width(void) const;
	virtual int get_height(void) const;
	virtual void print(ostream &o, const vector<const State *> *path) const;
#if defined(ENABLE_IMAGES)
	void export_eps(string file) const;
#endif	/* ENABLE_IMAGES */

private:
	bool on_path(const vector<const State *> *path, int x, int y) const;
	bool is_obstacle(int x, int y) const;

	enum { UNIT_COST, LIFE_COST } cost;

	int width, height;
	int start_x, start_y;
	int goal_x, goal_y;
	map<int, bool> obstacles;

#if defined(ENABLE_IMAGES)
	void expanded_state(const GridState *s);

	unsigned long expanded;
	vector<AtomicInt> states;
#endif	/* ENABLE_IMAGES */

};

#endif	/* !_GRID_WORLD_H_ */
