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
	  open(false),
	  incons(false),
	  f_pq_index(-1),
	  f_prime_pq_index(-1)
{
	free_avs = mem_freelist_create(5, 1, sizeof(struct atomic_vals));
	if (!free_avs) {
		perror(__func__);
		abort();
	}
	avs = NULL;
	avs = get_avs(p, g, c);
}

State::~State()
{
	mem_release(free_avs, avs);
	mem_freelist_destroy(free_avs);
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
 * Get the transition cost into this state.
 * \return g
 */
fp_type State::get_c(void)
{
	fp_type ret = fp_infinity;

	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(free_avs, &avs);
	ret = a->c;
	mem_release(free_avs, a);

	return ret;
}
/**
 * Get the cost so far of the state.
 * \return g
 */
fp_type State::get_g(void)
{
	fp_type ret = fp_infinity;

	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(free_avs, &avs);
	ret = a->g;
	mem_release(free_avs, a);

	return ret;
}

/**
 * Set the g value for this state.
 */
void State::update(State *p, fp_type c_val, fp_type g_val)
{
	struct atomic_vals *o, *n;

	n = get_avs(p, g_val, c_val);
	for ( ; ; ) {
		o = (struct atomic_vals*) mem_safe_read(free_avs, &avs);
		if (o->g <= n->g) {
			mem_release(free_avs, n);
			mem_release(free_avs, o);
			return;
		}

		if (compare_and_swap(&avs, (intptr_t) o, (intptr_t) n)) {
			mem_release(free_avs, o);
			mem_release(free_avs, o); // double release
			return;
		}

		mem_release(free_avs, o);
	}
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
 * Get the parent of this state.
 */
State *State::get_parent(void)
{
	State *ret = NULL;

	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(free_avs, &avs);
	ret = a->parent;
	mem_release(free_avs, a);

	return ret;
}


/**
 * Set the parent.
 */
void State::set_parent(State *p)
{
	struct atomic_vals *a =
		(struct atomic_vals*) mem_safe_read(free_avs, &avs);
	a->parent = p;
	mem_release(free_avs, a);
}

/**
 * Set the open status of the state.
 */
void State::set_open(bool b)
{
	open = b;
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
