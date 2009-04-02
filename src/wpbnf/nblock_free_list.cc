/**
 * \file nblock_free_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#include <assert.h>

#include <limits>
#include <algorithm>
#include <iostream>
#include <vector>

#include "../util/atomic_int.h"
#include "../pq_open_list.h"
#include "nblock.h"
#include "nblock_free_list.h"

using namespace std;
using namespace WPBNF;

NBlockFreeList::NBlockFreeList(void)
{
	make_heap(heap.begin(), heap.end(), NBlock::compare);
}

void NBlockFreeList::add(NBlock *b)
{
	assert(b->sigma == 0);

	heap.push_back(b);
	push_heap(heap.begin(), heap.end(), NBlock::compare);
	best.set(heap.front()->open_fp.peek()->get_f_prime());
}


NBlock *NBlockFreeList::take(void)
{
	NBlock *b;

	b = heap.front();
	pop_heap(heap.begin(), heap.end(), NBlock::compare);
	heap.pop_back();

	if (heap.empty())
		best.set(fp_infinity);
	else
		best.set(heap.front()->open_fp.peek()->get_f_prime());

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
			make_heap(heap.begin(), heap.end(), NBlock::compare);
			return;
		}
	}
}

fp_type NBlockFreeList::best_val(void)
{
	return best.read();
}


void NBlockFreeList::print(ostream &o)
{
	vector<NBlock *>::iterator iter;

	for (iter = heap.begin(); iter != heap.end(); iter++)
		(*iter)->print(o);
}
