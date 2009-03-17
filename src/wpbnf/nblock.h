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
	struct NBlock {

		/**
		 * Operations for the nblock PQ used for trakcing f_min.
		 */
		struct NBlockPQFuncs {
			/* Predecessor operator. */
			int inline operator()(NBlock *a, NBlock *b) {
				return a->open_f.get_best_val() < b->open_f.get_best_val();
			}
			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->pq_index = i;
			}
			/* Set the prio queue index. */
			int inline operator()(NBlock *a) {
				return a->pq_index;
			}
			/* Set the prio queue index. */
			fp_type inline get_value(NBlock *a) {
				return a->open_f.get_best_val();
			}
		};

		/**
		 * NBlocks compare on f', then f then g.
		 *
		 * This class is for the nblock_free_list.
		 */
		class NBlockCompare {
		public:
			bool operator()(NBlock *a, NBlock *b)
			{
				assert(!a->open_fp.empty());
				assert(!b->open_fp.empty());
				fp_type fpa = a->open_fp.get_best_val();
				fp_type fpb = b->open_fp.get_best_val();
				if (fpa == fpb) {
					fp_type fa = a->open_f.get_best_val();
					fp_type fb = b->open_f.get_best_val();
					if (fa == fb && !a->open_fp.empty() && !b->open_fp.empty())
						return a->open_fp.peek()->get_g() < b->open_fp.peek()->get_g();
					else
						return fa > fb;
				}
				return fpa > fpb;
			}
		};

		static NBlockCompare compare;


		NBlock(const Projection *p, unsigned int id);
		~NBlock(void);
		void next_iteration(void);
		bool operator<(NBlock *a);
		void print(ostream &s);


		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<State::PQOpsFPrime> open_fp;
		PQOpenList<State::PQOpsF> open_f;
		unsigned int sigma_hot;
		int hot;
		int inuse;
		int pq_index; // Index into the f_min PQ
		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
