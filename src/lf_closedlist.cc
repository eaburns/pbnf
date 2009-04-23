/**
 * \file lf_closedlist.cc
 *
 *
 *
 * \author eaburns
 * \date 2009-04-12
 */

#include "lf_closedlist.h"

extern "C" {
#include "nbds.0.4.3/include/common.h"
#include "nbds.0.4.3/include/map.h"
#include "nbds.0.4.3/include/hashtable.h"
}

LF_ClosedList::LF_ClosedList(void)
{
	map = map_alloc(&MAP_IMPL_HT, NULL);
}

LF_ClosedList::~LF_ClosedList(void)
{
	map_free(map);
}

void LF_ClosedList::add(State *s)
{
	map_set(map, (map_key_t) s->hash(), (map_val_t) s);
}

State *LF_ClosedList::lookup(State *s)
{
	State *t;

	t = (State *) map_get(map, (map_key_t) s->hash());
	if (t == DOES_NOT_EXIST)
		return NULL;

	return t;
}

void LF_ClosedList::delete_all_states(void)
{
	map_iter_t *it = map_iter_begin(map, 0);
	map_val_t vl;

	vl = map_iter_next(it, NULL);
	while (vl != DOES_NOT_EXIST) {
		State *s = (State *) vl;
		delete s;

		vl = map_iter_next(it, NULL);
	}

	map_iter_free(it);
}
