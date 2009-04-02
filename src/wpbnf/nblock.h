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
		 * Operations for the nblock PQ used for tracking f_min.
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

		struct NBlockPQFuncsFprime {
			/* Predecessor operator. */
			int inline operator()(NBlock *a, NBlock *b) {
				fp_type afp = a->open_fp.get_best_val();
				fp_type bfp = b->open_fp.get_best_val();

				if (afp == bfp) {
					fp_type af = a->open_f.get_best_val();
					fp_type bf = b->open_f.get_best_val();
					if (af == bf) {
						fp_type ag = fp_infinity;
						fp_type bg = fp_infinity;
						if (!a->open_fp.empty())
							ag = a->open_fp.peek()->get_g();
						if (!b->open_fp.empty())
							bg = b->open_fp.peek()->get_g();
						return ag > bg;
					}
					return af < bf;
				}
				return afp < bfp;
			}
			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->fp_pq_index = i;
			}
			/* Set the prio queue index. */
			int inline operator()(NBlock *a) {
				return a->fp_pq_index;
			}
			/* Set the prio queue index. */
			fp_type inline get_value(NBlock *a) {
				return a->open_fp.get_best_val();
			}
		};

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
		int fp_pq_index; // Index into the free list PQ
		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
