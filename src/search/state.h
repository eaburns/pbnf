/* -*- mode:linux -*- */
/**
 * \file state.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */
#if !defined(_STATE_H_)
#define _STATE_H_

#include <iostream>
#include <vector>

#include "search_domain.h"

using namespace std;

class State {
public:
	State(const SearchDomain *d, const State *parent, int g);

	virtual int hash(void) const = 0;
	virtual bool is_goal(void) const = 0;
	virtual State *clone(void) const = 0;
	virtual void print(ostream &o) const = 0;

	virtual vector<const State*> *expand(void) const;

	virtual int get_g(void) const;
	virtual int get_h(void) const;
	virtual void set_parent(const State *);
	virtual const State *get_parent(void) const;
protected:
	const State *parent;
	const SearchDomain *domain;
	float g;
	float h;
};

#endif	/* !_STATE_H_ */
