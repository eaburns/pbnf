/* -*- mode:linux -*- */
/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#if !defined(_NBLOCK_H_)
#define _NBLOCK_H_

#include <iostream>
#include <vector>

#include "../open_list.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

using namespace std;

/**
 * An NBlock
 */
struct NBlock {
	NBlock(unsigned int id,
	       vector<unsigned int> preds,
	       vector<unsigned int> succs);

	void next_iteration(void);

	void print(ostream &s) const;

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

#endif	/* !_NBLOCK_H_ */
