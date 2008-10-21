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

#include <vector>
#include <map>

#include "projection.h"
#include "nblock_factory.h"
#include "nblock_free_list.h"
#include "nblock.h"

using namespace std;

class NBlockGraph {
public:
	NBlockGraph(NBlockFactory *fact, NBlockFreeList *l, Projection *p);

	virtual ~NBlockGraph();

	NBlock *next_free_nblock(void);
	void acquire_nblock(unsigned int hash);
	void release_nblock(unsigned int hash);

private:
	void update_scope_sigmas(unsigned int y, int delta);
	void update_sigma(unsigned int y, int delta);

	vector<NBlock *> blocks;
	vector<unsigned int> sigmas;
	NBlockFreeList *free_list;
	map<unsigned int, vector<unsigned int> > preds;
	map<unsigned int, vector<unsigned int> > succs;
};

#endif	/* !_NBLOCK_GRAPH_H_ */
