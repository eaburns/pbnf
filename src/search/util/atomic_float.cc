/* -*- mode:linux -*- */
/**
 * \file atomic_float.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-10
 */

#include <assert.h>

#include "atomic_int.h"
#include "atomic_float.h"

union cast_union {
	unsigned long long ll;
	double d;
};

AtomicFloat::AtomicFloat(void)
{
	assert(sizeof(unsigned long long) == sizeof(double));
	set(0);
}

AtomicFloat::AtomicFloat(double v)
{
	assert(sizeof(unsigned long long) == sizeof(double));
	set(v);
}

double AtomicFloat::read(void)
{
	union cast_union c;
	c.ll = value.read();
	return c.d;
}

void AtomicFloat::set(double v)
{
	union cast_union c;
	c.d = v;
	value.set(c.ll);
}
