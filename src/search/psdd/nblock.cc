/* -*- mode:linux -*- */
/**
 * \file nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include <assert.h>

#include <vector>

#include "nblock.h"
#include "../open_list.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

using namespace std;

/**
 * Create a new NBlock structure.
 */
NBlock::NBlock(unsigned int id, vector<unsigned int> preds,
	       vector<unsigned int> succs)
	: id(id),
	  sigma(0),
	  cur_open(&open_a),
	  next_open(&open_b),
	  preds(preds),
	  succs(succs) {}


/**
 * Swap the current and next open lists in this NBlock.
 */
void NBlock::next_iteration(void)
{
	OpenList *tmp;

	assert(cur_open->empty());
	assert(sigma == 0);

	tmp = cur_open;
	cur_open = next_open;
	next_open = tmp;
}
