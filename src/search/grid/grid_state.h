/* -*- mode:linux -*- */
/**
 * \file grid_state.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#if !defined(_GRID_STATE_H_)
#define _GRID_STATE_H_

#include <vector>

#include "grid_world.h"
#include "../state.h"
#include "../search_domain.h"

using namespace std;

class GridState : public State {
public:
	GridState(const GridWorld *d, const State *parent, int g, int x, int y);

	virtual bool is_goal(void) const;
	virtual int hash(void) const;

	virtual int get_x(void) const;
	virtual int get_y(void) const;
private:
	int x, y;
};

#endif	/* !_GRID_STATE_H_ */
