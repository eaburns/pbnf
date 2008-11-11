/**
 * \file sparc64_atomic_int.cc
 *
 * \author Ethan Burns
 * \date 2008-10-22
 */

#include <assert.h>

#include "atomic_int.h"

extern "C" {
	extern int compare_and_swap(volatile unsigned long *addr, unsigned long *o, unsigned long n);
}

AtomicInt::AtomicInt(void)
	: value(0)
{
}

AtomicInt::AtomicInt(unsigned long val)
	: value(val)
{
	assert(sizeof(uint32_t) == sizeof(unsigned long));
}

unsigned long AtomicInt::read(void) const
{
	return value;
}

void AtomicInt::set(unsigned long i)
{
	value = i;
}

void AtomicInt::add(unsigned long i)
{
	unsigned long old = value;

	while (!compare_and_swap(&value, &old, old + i))
		;
}

void AtomicInt::sub(unsigned long i)
{
	unsigned long old = value;

	while (!compare_and_swap(&value, &old, old - i))
		;
}

void AtomicInt::inc(void)
{
	add(1);
}

void AtomicInt::dec(void)
{
	sub(1);
}

unsigned long AtomicInt::swap(unsigned long n)
{
	unsigned long old = value;

	while(!compare_and_swap(&value, &old, n))
		;

	return old;
}

unsigned long AtomicInt::cmp_and_swap(unsigned long o, unsigned long n)
{
	compare_and_swap(&value, &o, n);

	return o;
}

