/* -*- mode:linux -*- */
/**
 * \file tiles_state.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#if !defined(_TILES_STATE_H_)
#define _TILES_STATE_H_

#include <vector>

#include "../search_domain.h"
#include "../state.h"

using namespace std;

class TilesState : public State {
public:
	TilesState(SearchDomain *d, const State *parent, float g,
		   vector<unsigned int> tiles, unsigned int blank);

	TilesState(SearchDomain *d, const State *parent, float g,
		   float h, vector<unsigned int> tiles,
		   unsigned int blank);

	virtual bool is_goal(void) const;
	virtual int hash(void) const;
	virtual State *clone(void) const;
	virtual void print(ostream &o) const;
	virtual bool equals(const State *s) const;

	vector<unsigned int> get_tiles(void) const;
	unsigned int get_blank(void) const;
private:
	vector<unsigned int> tiles;
	unsigned int blank;
};

#endif	/* !_TILES_STATE_H_ */
