/* -*- mode:linux -*- */
/**
 * \file nblock_graph.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_NBLOCK_GRAPH_H_)
#define _NBLOCK_GRAPH_H_

#include <map>
#include <queue>
#include <vector>

#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "projection.h"

using namespace std;

class NBlockGraph {
public:
	NBlockGraph(Projection *p);

	virtual ~NBlockGraph();

private:
	void update_scope_sigmas(unsigned int y, int delta);
	void update_sigma(unsigned int y, int delta);

	struct NBlock {
		NBlock(void);

		unsigned int sigma;
		ClosedList closed;
		QueueOpenList open_a;
		QueueOpenList open_b;
		OpenList *cur_open;
		OpenList *next_open;
		vector<unsigned int> preds;
		vector<unsigned int> succs;
	};

	/* NBlocks. */
	map<unsigned int, NBlock *> blocks;

	/* list of free nblock numbers */
	queue<unsigned int> free_list;
};

#endif	/* !_NBLOCK_GRAPH_H_ */
