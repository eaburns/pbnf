/**
 * \file dynamic_bounded_psdd.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-27
 */

#if !defined(_DYNAMIC_BOUNDED_PSDD_H_)
#define _DYNAMIC_BOUNDED_PSDD_H_

#include "search.h"
#include "state.h"

class DynamicBoundedPSDD : public Search {
public:
        DynamicBoundedPSDD(unsigned int n_threads, float weight);

	virtual ~DynamicBoundedPSDD(void);
	virtual vector<State *> *search(State *s);
private:
	unsigned int n_threads;
	float weight;
};

#endif	/* !_DYNAMIC_BOUNDED_PSDD_H_ */
