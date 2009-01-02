/*
 * \file atomic_int_test.cc
 *
 * \author Ethan Burns
 * \date 2008-10-22
 */

#include <iostream>

#include "atomic_int.h"

using namespace std;

int main(void)
{
  int ret;
  AtomicInt i(1);

  cerr << "initial i (1): " << i.read() << endl;

  i.inc();
  cerr << "inc i (2): " << i.read() << endl;

  i.dec();
  cerr << "dec i (1): " << i.read() << endl;

  i.set(42);
  cerr << "set i (42): " << i.read() << endl;

  i.sub(2);
  cerr << "sub i (40): " << i.read() << endl;

  i.add(2);
  cerr << "add i (42): " << i.read() << endl;

  ret = i.swap(50);
  cerr << "swap i (50), return (42): " << i.read() << ", " << ret << endl;

  ret = i.cmp_and_swap(42, 1);
  cerr << "bad cmp_and_swap i (50), return (50): " << i.read() << ", " << ret << endl;

  ret = i.cmp_and_swap(50, 1);
  cerr << "good cmp_and_swap i (1), return (50): " << i.read() << ", " << ret << endl;

  return 0;
}
