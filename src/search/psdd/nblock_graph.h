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

#include <pthread.h>

#include <map>
#include <list>
#include <vector>

#include "../state.h"
#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "projection.h"

using namespace std;

struct NBlock {
	NBlock(unsigned int id,
	       vector<unsigned int> preds,
	       vector<unsigned int> succs);

	void next_iteration(void);

	unsigned int id;
	unsigned int sigma;
	ClosedList closed;
	QueueOpenList open_a;
	QueueOpenList open_b;
	OpenList *cur_open;
	OpenList *next_open;
	vector<unsigned int> preds;
	vector<unsigned int> succs;
};


class NBlockGraph {
public:
	NBlockGraph(Projection *p, const State *init);

	~NBlockGraph();

	NBlock *next_nblock(NBlock *finished);

private:
	void update_scope_sigmas(unsigned int y, int delta);
	void update_sigma(unsigned int y, int delta);

	/* NBlocks. */
	map<unsigned int, NBlock *> blocks;

	/* The total number of NBlocks. */
	unsigned int num_nblocks;

	/* The number of NBlocks with sigma values of zero. */
	unsigned int num_sigma_zero;

	/* list of free nblock numbers */
	list<NBlock *> free_list_a;
	list<NBlock *> free_list_b;

	list<NBlock *> *cur_free_list;
	list<NBlock *> *next_free_list;

	pthread_mutex_t mutex;
	pthread_cond_t cond;
};

#endif	/* !_NBLOCK_GRAPH_H_ */
