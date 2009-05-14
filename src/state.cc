/**
 * \file state.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#include <assert.h>

#include "state.h"

extern "C" {
#include "lockfree/include/mem.h"
#include "lockfree/include/atomic.h"
}

struct State::atomic_vals *State::get_avs(State *p, fp_type g, fp_type c)
{
	struct atomic_vals *a;

	a = (struct atomic_vals*) mem_new(free_avs);

	if (!a) {
		perror(__func__);
		abort();
	}

	a->parent = p;
	a->g = g;
	a->c = c;

	return a;
}

State::State(SearchDomain *d, State *p, fp_type c, fp_type g)
	: domain(d),
	  h(-1),
	  lockfree(false),
	  open(false),
	  incons(false),
	  f_pq_index(-1),
	  f_prime_pq_index(-1)
{
	if (p)
		lockfree = p->lockfree;


	if (lockfree) {
		free_avs = mem_freelist_create(10, 1, sizeof(struct atomic_vals));
		if (!free_avs) {
			perror(__func__);
			abort();
		}
		avs = NULL;
		avs = get_avs(p, g, c);

		get_c_fun = __lf_get_c;
		get_g_fun = __lf_get_g;
		set_parent_fun = __lf_set_parent;
		get_parent_fun = __lf_get_parent;
		update_fun = __lf_update;


	} else {
		this->g = g;
		this->parent = p;
		this->c = c;

		get_c_fun = __get_c;
		get_g_fun = __get_g;
		set_parent_fun = __set_parent;
		get_parent_fun = __get_parent;
		update_fun = __update;

	}
}

State::~State()
{
	if (lockfree) {
		mem_release(free_avs, avs);
		mem_freelist_destroy(free_avs);
	}
}

/**
 * Get the search domain for this state.
 */
SearchDomain *State::get_domain(void) const
{
	return domain;
}

/**
 * Get the estimated cost of a path that uses this node.
 * \return g + h
 */
fp_type State::get_f(void)
{
	return get_g() + h;
}

/**
 * Get the estimated cost of a path that uses this node.
 * \return g + wh
 */
fp_type State::get_f_prime(void)
{
	return get_g() + ((domain->get_heuristic()->get_weight() * h) / fp_one);
}

/**
 * Get the estimated cost to go.
 * \return h
 */
fp_type State::get_h(void) const
{
	assert(h >= 0.0);
	return h;
}

/**
 * Expand the given state.
 * \return A newly allocated vector of the children states.  This must
 *         be deleted by the caller.
 */
vector<State*> *State::expand(void)
{

	return domain->expand(this);
}

/**
 * Follow the parent links back up and create copies of each state.
 * \return A path from the initial state to the goal state.  This
 *         vector and the states within it must be deleted by the
 *         caller.  All of the states on the returned path are clones
 *         of the states from the search, so those states can be
 *         deleted separately.
 */
vector<State *> *State::get_path(void)
{
	vector<State *> *path = new vector<State *>;
	State *p;
	State *copy, *last = NULL;

	for (p = this; p; p = p->get_parent()) {
		copy = p->clone();
		copy->set_parent(NULL);

		if (last)
			last->set_parent(copy);

		path->push_back(copy);
		last = copy;
	}

	return path;
}

/**
 * Set the open status of the state.
 */
void State::set_open(bool b)
{
	open = b;
}

/**
 * Set the incons status of the state.
 */
void State::set_incons(bool b)
{
	incons = b;
}

/**
 * Test if the state is open.
 */
bool State::is_open(void) const
{
	return open;
}

bool State::is_incons(void) const
{
	return incons;
}

void State::set_lockfree(bool b)
{
	lockfree = b;
}

// -----------------------------------------------

fp_type State::__get_c(State *t)
{
	return t->c;
}

fp_type State::__lf_get_c(State *t)
{
	fp_type ret = fp_infinity;


	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(t->free_avs, &t->avs);
	ret = a->c;
	mem_release(t->free_avs, a);

	return ret;
}

fp_type State::__get_g(State *t)
{
	return t->g;
}

fp_type State::__lf_get_g(State *t)
{
	fp_type ret = fp_infinity;

	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(t->free_avs, &t->avs);
	ret = a->g;
	mem_release(t->free_avs, a);

	return ret;
}

void State::__update(State *t, State *p, fp_type c_val, fp_type g_val)
{
	assert(t->g > g_val);
	t->g = g_val;
	t->c = c_val;
	t->parent = p;
}

void State::__lf_update(State *t, State *p, fp_type c_val, fp_type g_val)
{
	struct atomic_vals *o, *n;

	n = t->get_avs(p, g_val, c_val);
	for ( ; ; ) {
		o = (struct atomic_vals*) mem_safe_read(t->free_avs, &t->avs);
		if (o->g <= n->g) {
			mem_release(t->free_avs, n);
			mem_release(t->free_avs, o);
			return;
		}

		if (compare_and_swap(&t->avs, (intptr_t) o, (intptr_t) n)) {
			mem_release(t->free_avs, o);
			mem_release(t->free_avs, o); // double release
			return;
		}

		mem_release(t->free_avs, o);
	}
}

State *State::__get_parent(State *t)
{
	return t->parent;
}

State *State::__lf_get_parent(State *t)
{
	State *ret = NULL;

	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(t->free_avs, &t->avs);
	ret = a->parent;
	mem_release(t->free_avs, a);

	return ret;
}

void State::__set_parent(State *t, State *p)
{
	t->parent = p;
}

void State::__lf_set_parent(State *t, State *p)
{
	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(t->free_avs, &t->avs);
	a->parent = p;
	mem_release(t->free_avs, a);
}
