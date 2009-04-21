/**
 * \file nblock_free_list.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-04-18
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
using namespace OPBNF;

NBlockFreeList::NBlockFreeList(void)
{
	make_heap(heap_fp.begin(), heap_fp.end(), NBlock::compare_fp);
	make_heap(heap_f.begin(), heap_f.end(), NBlock::compare_f);
}

void NBlockFreeList::add(NBlock *b)
{
	assert(b->sigma == 0);

	heap_fp.push_back(b);
	push_heap(heap_fp.begin(), heap_fp.end(), NBlock::compare_fp);
	best_fp.set(heap_fp.front()->open_fp.peek()->get_f_prime());

	heap_f.push_back(b);
	push_heap(heap_f.begin(), heap_f.end(), NBlock::compare_f);
	best_f.set(heap_f.front()->open_f.peek()->get_f());
}


NBlock *NBlockFreeList::take_fp(void)
{
	NBlock *b;

	b = heap_fp.front();
	pop_heap(heap_fp.begin(), heap_fp.end(), NBlock::compare_fp);
	heap_fp.pop_back();

	vector<NBlock *>::iterator iter;

	for (iter = heap_f.begin(); iter != heap_f.end(); iter++) {
		if (*iter == b) {
			heap_f.erase(iter);
			make_heap(heap_f.begin(), heap_f.end(), NBlock::compare_f);
			break;
		}
	}

	if (heap_fp.empty()){
		best_fp.set(fp_infinity);
		best_f.set(fp_infinity);
	}
	else{
		best_fp.set(heap_fp.front()->open_fp.peek()->get_f_prime());
		best_f.set(heap_f.front()->open_f.peek()->get_f());
	}

	return b;
}

NBlock *NBlockFreeList::take_f(void)
{
	NBlock *b;

	b = heap_f.front();
	pop_heap(heap_f.begin(), heap_f.end(), NBlock::compare_f);
	heap_f.pop_back();

	vector<NBlock *>::iterator iter;

	for (iter = heap_fp.begin(); iter != heap_fp.end(); iter++) {
		if (*iter == b) {
			heap_fp.erase(iter);
			make_heap(heap_fp.begin(), heap_fp.end(), NBlock::compare_fp);
			break;
		}
	}

	if (heap_fp.empty()){
		best_fp.set(fp_infinity);
		best_f.set(fp_infinity);
	}
	else{
		best_fp.set(heap_fp.front()->open_fp.peek()->get_f_prime());
		best_f.set(heap_f.front()->open_f.peek()->get_f());
	}

	return b;
}


bool NBlockFreeList::empty(void) const
{
	return heap_fp.empty();
}


void NBlockFreeList::remove(NBlock *b)
{
	vector<NBlock *>::iterator iter;

	for (iter = heap_fp.begin(); iter != heap_fp.end(); iter++) {
		if (*iter == b) {
			heap_fp.erase(iter);
			make_heap(heap_fp.begin(), heap_fp.end(), NBlock::compare_fp);
			break;
		}
	}

	for (iter = heap_f.begin(); iter != heap_f.end(); iter++) {
		if (*iter == b) {
			heap_f.erase(iter);
			make_heap(heap_f.begin(), heap_f.end(), NBlock::compare_f);
			break;
		}
	}
}

fp_type NBlockFreeList::best_fp_val(void)
{
	return best_fp.read();
}

fp_type NBlockFreeList::best_f_val(void)
{
	return best_f.read();
}


void NBlockFreeList::print(ostream &o)
{
	vector<NBlock *>::iterator iter;

	for (iter = heap_fp.begin(); iter != heap_fp.end(); iter++)
		(*iter)->print(o);

	for (iter = heap_f.begin(); iter != heap_f.end(); iter++)
		(*iter)->print(o);
}
