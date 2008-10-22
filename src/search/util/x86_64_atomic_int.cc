/* -*- mode:linux -*- */
/**
 * \file x86_64_atomic_int.cc
 *
 * Atomic integer operations.  This code uses code from
 * liblinuxkernel, which means that it was indirrectly taken from the
 * Linux kernel.
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include "atomic_int.h"

#define LOCK_PREFIX    "lock;"

AtomicInt::AtomicInt(unsigned int val)
{
  value = val;
}

unsigned int AtomicInt::read(void) const
{
  return value;
}

void AtomicInt::set(unsigned int i)
{
  value = i;
}

void AtomicInt::add(unsigned int i)
{
  __asm__ __volatile__(LOCK_PREFIX "addl %1,%0"
		       :"=m"(value)
		       :"ir"(i), "m"(value));
}

void AtomicInt::sub(unsigned int i)
{
  __asm__ __volatile__(LOCK_PREFIX "subl %1,%0"
		       :"=m"(value)
		       :"ir"(i), "m"(value));
}

void AtomicInt::inc(void)
{
  __asm__ __volatile__(LOCK_PREFIX "incl %0"
		       :"=m"(value)
		       :"m"(value));
}

void AtomicInt::dec(void)
{
  __asm__ __volatile__(LOCK_PREFIX "decl %0"
		       :"=m"(value)
		       :"m"(value));
}

unsigned int AtomicInt::swap(unsigned int n)
{
  __asm__ __volatile__("xchgl %0,%1"
		       : "=r" (n)
		       : "m" (value), "0" (n)
		       : "memory");

  return n;
}

unsigned int AtomicInt::cmp_and_swap(unsigned int o, unsigned int n)
{
  unsigned int prev;

  __asm__ __volatile__("cmpxchgl %1,%2"
		       : "=a"(prev)
		       : "r"(n), "m"(value), "0"(o)
		       : "memory");
  return prev;
}
