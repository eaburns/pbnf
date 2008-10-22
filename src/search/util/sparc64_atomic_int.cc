/**
 * \file sparc64_atomic_int.cc
 *
 * \author Ethan Burns
 * \date 2008-10-22
 */

#include <assert.h>

#include "atomic_int.h"

extern "C" {
  extern int compare_and_swap(volatile uint32_t *addr, uint32_t *o, uint32_t n);
}

AtomicInt::AtomicInt(unsigned int val)
  : value(val) {}

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
  uint32_t old = value;

  while (!compare_and_swap(&value, &old, old + i))
    ;
}

void AtomicInt::sub(unsigned int i)
{
  uint32_t old = value;

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

unsigned int AtomicInt::swap(unsigned int n)
{
  uint32_t old = value;

  while(!compare_and_swap(&value, &old, n))
    ;

  return old;
}

unsigned int AtomicInt::cmp_and_swap(unsigned int o, unsigned int n)
{
  compare_and_swap(&value, &o, n);

  return o;
}

