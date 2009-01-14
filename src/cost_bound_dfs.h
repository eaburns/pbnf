/**
 * \file cost_bound_dfs.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_COST_BOUND_DFS_H_)
#define _COST_BOUND_DFS_H_

#include <vector>

#include "state.h"
#include "search.h"

using namespace std;

/**
 * A Depth First Search that is bounded on node cost.
 */
class CostBoundDFS : public Search {
public:
	CostBoundDFS(float bound);

	virtual vector<State *> *search(State *);

	float get_min_pruned(void) const;
private:
	bool is_cycle(State *) const;

	float bound;
	float min_pruned;
};

#endif	/* !_COST_BOUND_DFS_H_ */
