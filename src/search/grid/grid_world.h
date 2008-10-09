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
#include <vector>

#include "../state.h"
#include "../search_domain.h"

using namespace std;

class GridWorld : public SearchDomain {
public:
	GridWorld(istream &s);
	~GridWorld();

	virtual State *initial_state(void);
	virtual vector<const State*> *expand(const State *s) const;

	virtual int get_goal_x(void) const;
	virtual int get_goal_y(void) const;
	virtual int get_width(void) const;
	virtual int get_height(void) const;
	virtual void print(ostream &o) const;
private:
	int hash_position(int x, int y) const;
	bool is_obstacle(int x, int y) const;

	int width, height;
	int start_x, start_y;
	int goal_x, goal_y;
	bool *obstacles;
};

#endif	/* !_GRID_WORLD_H_ */
