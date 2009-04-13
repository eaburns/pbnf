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
#include "common.h"
#include "datatype.h"
#include "map.h"
#include "hashtable.h"
}

static int state_cmp(void *, void *);
static void *state_clone(void *);
static uint32_t state_hash(void *);

const datatype_t state_datatype = {
	state_cmp,
	state_hash,
	state_clone
};

static int state_cmp(void *_a, void *_b)
{
	State *a = (State *)_a;
	State *b = (State *)_b;

	if (a->equals(b))
		return 0;
	else
		return a - b;
}

static void *state_clone(void *_s)
{
	State *s = (State *) _s;

	return s->clone();
}

static uint32_t state_hash(void *_s)
{
	State *s = (State *) _s;

	return (uint32_t) s->hash();
}

LF_ClosedList::LF_ClosedList(void)
{
	map = map_alloc(&MAP_IMPL_HT, &state_datatype);
}

LF_ClosedList::~LF_ClosedList(void)
{
	map_free(map);
}

void LF_ClosedList::add(State *s)
{
	map_add(map, (map_key_t) s, (map_val_t) s);
}

State *LF_ClosedList::lookup(State *s)
{
	State *t;

	t = (State *) map_get(map, (map_key_t) s);
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
