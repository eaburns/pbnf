/**
 * \file nblock.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-04-18
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

namespace OPBNF {
	struct NBlock {

		/**
		 * Operations for the nblock PQ used for trakcing f_min.
		 */
		struct NBlockPQFuncsFP {
			/* Predecessor operator. */
			int inline operator()(NBlock *a, NBlock *b) {
				return a->open_fp.get_best_val() < b->open_fp.get_best_val();
			}
			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->index_fp = i;
			}
			/* Set the prio queue index. */
			int inline operator()(NBlock *a) {
				return a->index_fp;
			}
			/* Set the prio queue index. */
			fp_type inline get_value(NBlock *a) {
				return a->open_fp.get_best_val();
			}
		};

		/**
		 * Operations for the nblock PQ used for trakcing f_min.
		 */
		struct NBlockPQFuncsF {
			/* Predecessor operator. */
			int inline operator()(NBlock *a, NBlock *b) {
				return a->open_f.get_best_val() < b->open_f.get_best_val();
			}
			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->index_f = i;
			}
			/* Set the prio queue index. */
			int inline operator()(NBlock *a) {
				return a->index_f;
			}
			/* Set the prio queue index. */
			fp_type inline get_value(NBlock *a) {
				return a->open_f.get_best_val();
			}
		};

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


		static bool better(NBlock* a, NBlock* b, fp_type bound);
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
		int pq_index;
		int index_fp;
		int index_f;
		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
