/* -*- mode:linux -*- */
/**
 * \file atomic_int.h
 *
 * Atomic integer operations.  This code uses code from
 * liblinuxkernel, which means that it was indirrectly taken from the
 * Linux kernel.
 *
 * \author Ethan Burns
 * \date 2008-10-14
 */

#if !defined(_ATOMIC_INT_H_)
#define _ATOMIC_INT_H_

#include "stdint.h"
/**
 * This class defines an atomic integer.  The operations provided as
 * methods of this class can be used concurrently by multiple
 * processors to access this interger value.
 *
 * \note A these methods are currently x86 specific.  Unfortunately we
 *       will need to add pre-processor macros to make them portable.
 */
class AtomicInt {
public:
	AtomicInt(void);

	AtomicInt(unsigned long val);

	unsigned long read(void) const;

	void set(unsigned long i);

	void add(unsigned long i);

	void sub(unsigned long i);

	void inc(void);

	void dec(void);

	unsigned long swap(unsigned long n);

	/**
	 * Atomic compare and swap.  This operation takes an old value
	 * and a new value.  If the AtomicInt currently contains the
	 * old value passed as a parameter here, the new value is
	 * atomically swapped in.  If the AtomicInt contains a value
	 * that is not the old value given as a parameter, the new
	 * value is *not* swapped in.
	 * \param o The expected old value.
	 * \param n The new value to swap if the current value is 'o'.
	 * \return The value before this operation.  If the return
	 *         value is equivilant to 'o', then the operation was
	 *         a success, otherwise it was not.
	 */
	unsigned long cmp_and_swap(unsigned long o, unsigned long n);
private:
	volatile unsigned long value;
};

#endif	/* !_ATOMIC_INT_H_ */
