/* -*- mode:linux -*- */
/**
 * \file nblock_free_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#include <assert.h>

#include <algorithm>
#include <vector>

#include "nblock.h"
#include "nblock_free_list.h"

using namespace std;
using namespace PBNF;


void NBlockFreeList::add(NBlock *b)
{
	assert(b->sigma == 0);

	heap.push_back(b);
	push_heap(heap.begin(), heap.end());
}


NBlock *NBlockFreeList::take(void)
{
	NBlock *b;

	b = heap.front();
	pop_heap(heap.begin(), heap.end());

	return b;
}


bool NBlockFreeList::empty(void) const
{
	return heap.empty();
}


void NBlockFreeList::remove(NBlock *b)
{
	vector<NBlock *>::iterator iter;

	for (iter = heap.begin(); iter != heap.end(); iter++) {
		if (*iter == b) {
			heap.erase(iter);
			make_heap(heap.begin(), heap.end());
			return;
		}
	}
}

float NBlockFreeList::best_f(void)
{
	return heap.front()->open.peek()->get_f();
}
