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

#include <assert.h>

#include <iostream>
#include <vector>

#include "util/fixed_point.h"
#include "search_domain.h"

using namespace std;

extern "C" {
#include "lockfree/include/mem.h"
}

/**
 * An abstract search state class.
 */
class State {
public:

	class PQOpsF {
	public:
		/* The predecessor operator. */
		int inline operator()(State *a, State *b) const {
			fp_type fa = a->get_f();
			fp_type fb = b->get_f();

			if (fa < fb) return true;
			else if (fa > fb) return false;
			else {
				fp_type ga = a->get_g();
				fp_type gb = b->get_g();

				return ga > gb;
			}
		}
		fp_type inline get_value(State *s) const {
			return s->get_f();
		}
		void inline operator()(State *a, int i)
		{
			a->f_pq_index = i;
		}

		int inline operator()(State *a)
		{
			return a->f_pq_index;
		}
	};

	class PQOpsFPrime {
	public:
		int inline operator()(State *a, State *b) const {
			fp_type fa = a->get_f_prime();
			fp_type fb = b->get_f_prime();
			if (fa < fb) return true;
			else if (fa > fb) return false;
			else return f_cmp(a, b);
		}

		fp_type inline get_value(State *s) const {
			return s->get_f_prime();
		}
		void inline operator()(State *a, int i)
		{
			a->f_prime_pq_index = i;
		}

		int inline operator()(State *a)
		{
			return a->f_prime_pq_index;
		}
	private:
		PQOpsF f_cmp;
	};

	State(SearchDomain *d, State *parent, fp_type c, fp_type g);

	virtual ~State();

	virtual SearchDomain *get_domain(void) const;

	virtual uint64_t hash(void) const = 0;
	virtual bool is_goal(void) = 0;
	virtual State *clone(void) = 0;
	virtual void print(ostream &o) = 0;
	virtual bool equals(State *s) const = 0;

	virtual vector<State*> *expand(void);

	fp_type get_f(void);
	fp_type get_f_prime(void);
	fp_type get_h(void) const;
	vector<State *> *get_path(void);
	void set_open(bool b);
	void set_incons(bool b);
	bool is_open(void) const;
	bool is_incons(void) const;

	void set_lockfree(bool);

	/* use indirection for lockfree switching */
	inline fp_type get_c(void)
	{
		assert(get_c_fun);
		return get_c_fun(this);
	}

	inline fp_type get_g(void)
	{
		assert(get_g_fun);
		return get_g_fun(this);
	}

	inline void set_parent(State *p)
	{
		assert(set_parent_fun);
		set_parent_fun(this, p);
	}

	inline State *get_parent(void)
	{
		assert(get_parent_fun);
		return get_parent_fun(this);
	}

	inline void update(State *parent, fp_type c, fp_type g)
	{
		assert(update_fun);
		update_fun(this, parent, c, g);
	}


protected:

	SearchDomain *domain;
	fp_type h;

	bool lockfree;

	/* --------------------
	 * For the lock-free state representation.
	 */
	/* values that must be atomically updated. */
	struct atomic_vals {
		struct node n;
		State *parent;
		fp_type g;
		fp_type c;
	};
	struct atomic_vals *get_avs(State *p, fp_type g, fp_type c);

	struct atomic_vals *avs;
	freelist *free_avs;

	static fp_type __lf_get_c(State *);
	static fp_type __lf_get_g(State *);
	static void __lf_set_parent(State *, State *p);
	static State *__lf_get_parent(State *);
	static void __lf_update(State *, State *parent, fp_type c, fp_type g);
	/* -------------------- */

	/* --------------------
	 * For the non-lock-free state representation.
	 */
	fp_type g;
	fp_type c;
	State *parent;

	static fp_type __get_c(State *);
	static fp_type __get_g(State *);
	static void __set_parent(State *, State *p);
	static State *__get_parent(State *);
	static void __update(State *, State *parent, fp_type c, fp_type g);
	/* -------------------- */


	/* Provides indirection to avoid testing the lockfree
	 * condition. */
	fp_type (*get_c_fun)(State *);
	fp_type (*get_g_fun)(State *);
	void (*set_parent_fun)(State *, State *);
	State *(*get_parent_fun)(State *);
	void (*update_fun)(State *, State *parent, fp_type c, fp_type g);

	bool open;
	bool incons;

	/* indexes into the pq open lists. */
	int f_pq_index;
	int f_prime_pq_index;
};

#endif	/* !_STATE_H_ */
