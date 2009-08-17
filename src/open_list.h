/**
 * \file open_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_OPEN_LIST_H_)
#define _OPEN_LIST_H_

#include <ostream>
#include <list>

#include "util/fixed_point.h"
#include "util/atomic_float.h"
#include "util/cumulative_ave.h"

#include "state.h"

/**
 * Defines the interface to an OpenList.
 */
class OpenList {
public:
	OpenList();
	virtual ~OpenList();

	virtual void add(State *s) = 0;
	virtual State *take(void) = 0;
	virtual State *peek(void) = 0;
	virtual bool empty(void) = 0;
	virtual void delete_all_states(void) = 0;
	virtual void prune(void) = 0;
	virtual unsigned int size(void);

	/**
	 * Get all states.
	 */
	virtual list<State*> *states(void) = 0;

	virtual fp_type get_best_val(void);

	/* Print statistic information. */
	void print_stats(ostream &o);

#if defined(INSTRUMENTED)
	/* Get statistic information. */
	float get_avg_size(void);
	unsigned int get_max_size(void);
#endif	/* INSTRUMENTED */

protected:
	void set_best_val(fp_type f);

	/*
	 * set_size() and change_size() are provided so that
	 * statistics can be tracked about open list sizes.
	 */
	/* Set the size of the open list */
	void set_size(unsigned int i);

	/* change the size by a delta */
	void change_size(unsigned int d);

private:
	AtomicInt best;

	/* Statistic tracking for open list sizes. */
	unsigned int cur_size;
	unsigned int max_size;
	CumulativeAverage avg_size;
};

#endif	/* !_OPEN_LIST_H_ */
