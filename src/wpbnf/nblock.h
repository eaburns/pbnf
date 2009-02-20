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

#include <pthread.h>
#include <iostream>
#include <set>

#include "../open_list.h"
#include "../pq_open_list.h"
#include "../closed_list.h"
#include "../projection.h"

using namespace std;

namespace WPBNF {
/**
 * An NBlock
 */
	struct NBlock {

		struct NBlockPQFuncs {
			/* Order nblocks on increasing f-values. */
			int inline operator()(NBlock *a, NBlock *b) {
				fp_type fa, fb;

				if (a->open.empty())
					fa = fp_infinity;
				else
					fa = a->open.peek()->get_f();

				if (b->open.empty())
					fb = fp_infinity;
				else
					fb = b->open.peek()->get_f();

				if (fa > fb)
					return 1;
				else if (fb > fa)
					return -1;
				else
					return 0;
			}

			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->pq_index = i;
			}
		};

		NBlock(const Projection *p, unsigned int id);

		~NBlock(void);

		void next_iteration(void);
		bool operator<(NBlock *a);
		void print(ostream &s);

		struct NBlockCompare {
			bool operator()(NBlock *a, NBlock *b)
			{
				assert(!a->open.empty());
				assert(!b->open.empty());
				fp_type fa = a->open.peek()->get_f();
				fp_type fb = b->open.peek()->get_f();
				if (fa == fb)
					return a->open.peek()->get_g() < b->open.peek()->get_g();
				return fa > fb;
			}
		};

		static NBlockCompare compare;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<State::CompareOnFPrime> open;

		unsigned int sigma_hot;
		int hot;
		int inuse;

		int pq_index;

		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
