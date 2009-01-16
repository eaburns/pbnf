/**
 * \file atomic_int.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-10
 */

#include <assert.h>

#include "fixed_point.h"

#include "atomic_int.h"
#include "atomic_float.h"

union cast_union {
	unsigned int l;
	fp_type f;
};

AtomicFloat::AtomicFloat(void)
{
	assert(sizeof(unsigned int) == sizeof(fp_type));
	set(0);
}

AtomicFloat::AtomicFloat(float v)
{
	assert(sizeof(unsigned int) == sizeof(fp_type));
	set(v);
}

float AtomicFloat::read(void)
{
	union cast_union c;
	c.l = value.read();
	return c.f;
}

void AtomicFloat::set(float v)
{
	union cast_union c;
	c.f = v;
	value.set(c.l);
}
