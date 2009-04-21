/**
 * \file nblock_free_list.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-04-18
 */

#if !defined(_NBLOCK_FREE_LIST_H_)
#define _NBLOCK_FREE_LIST_H_

#include <iostream>
#include <vector>

#include "../util/atomic_int.h"
#include "nblock.h"

using namespace std;

namespace OPBNF {
	class NBlockFreeList {
	public:
		NBlockFreeList(void);

		void add(NBlock *b);
		NBlock *take_fp(void);
		NBlock *take_f(void);
		bool empty(void) const;
		void remove(NBlock *b);
		fp_type best_fp_val(void);
		fp_type best_f_val(void);
		void print(ostream &o);
	private:
		vector<NBlock *> heap_f;
		AtomicInt best_f;
		vector<NBlock *> heap_fp;
		AtomicInt best_fp;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_FREE_LIST_H_ */
