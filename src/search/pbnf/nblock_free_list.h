/* -*- mode:linux -*- */
/**
 * \file nblock_free_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#if !defined(_NBLOCK_FREE_LIST_H_)
#define _NBLOCK_FREE_LIST_H_

#include <iostream>
#include <vector>

#include "nblock.h"

using namespace std;

namespace PBNF {
	class NBlockFreeList {
	public:
		NBlockFreeList(void);

		void add(NBlock *b);
		NBlock *take(void);
		bool empty(void) const;
		void remove(NBlock *b);
		float best_f(void);
		void print(ostream &o);
	private:
		vector<NBlock *> heap;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_FREE_LIST_H_ */
