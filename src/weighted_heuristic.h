/**
 * \file weighted_heuristic.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-27
 */

#if !defined(_WEIGHTED_HEURISTIC_H_)
#define _WEIGHTED_HEURISTIC_H_

#include "state.h"
#include "heuristic.h"

class WeightedHeuristic : public Heuristic {
public:
	WeightedHeuristic(const SearchDomain *d, const Heuristic *h, float w);
	virtual ~WeightedHeuristic(void);

	virtual float compute(State *s) const;
private:
	float weight;
	const Heuristic *heuristic;
};

#endif	/* !_WEIGHTED_HEURISTIC_H_ */
