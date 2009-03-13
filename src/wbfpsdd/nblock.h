/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#if !defined(_WBFPSDD_NBLOCK_H_)
#define _WBFPSDD_NBLOCK_H_

#include <iostream>
#include <set>

#include "../pq_open_list.h"
#include "../closed_list.h"

using namespace std;

namespace WBFPSDD {

	struct NBlock {

		struct PQOpsF {
                        /* Order nblocks on increasing f-values. */
			int inline operator()(NBlock *a, NBlock *b) {
				fp_type fa, fb;
				fa = a->open_f.get_best_val();
				fb = b->open_f.get_best_val();
				/* if fa > fb, we want it to be
				 * ordered after fb in the PQ (which
				 * is a max PQ) so we say that fa is
				 * less than fb. */
				if (fa > fb) return -1;
 				else if (fb > fa) return 1;
				else return 0;
			}
			/* Set the prio queue index. */
			void inline operator()(NBlock *a, int i) {
				a->f_pq_index = i;
			}
			/* Set the prio queue index. */
			int inline operator()(NBlock *a) {
				return a->f_pq_index;
			}
			/* Set the prio queue index. */
			fp_type inline get_value(NBlock *a) {
				return a->open_f.get_best_val();
			}
		};

		struct PQOpsFPrime {
                        /* Order nblocks on increasing f-values. */
			int inline operator()(NBlock *a, NBlock *b) {
				fp_type fa, fb;
				fa = a->open_fp.get_best_val();
				fb = b->open_fp.get_best_val();
				if (fa > fb) return -1;
 				else if (fb > fa) return 1;
				else return f_cmp(a, b);
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

		private:
			PQOpsF f_cmp;

		};


		NBlock(const Projection *project, unsigned int id);

		~NBlock(void);

		void print(ostream &s) const;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<State::PQOpsF> open_f;
		PQOpenList<State::PQOpsFPrime> open_fp;
		int f_pq_index;	/* this nblock's index into a PQ */
		int fp_pq_index; /* this nblock's index into a PQ */

		bool inuse;

		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};


} /* WBFPSDD */

#endif	/* !_WBFPSDD_NBLOCK_H_ */
