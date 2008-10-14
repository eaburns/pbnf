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

#define LOCK_PREFIX    "lock;"

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
	AtomicInt(int val) { value = val; }

	inline int read(void) const { return value; }

	inline void set(int i) { value = i; }

	inline void add(int i) {
		__asm__ __volatile__(LOCK_PREFIX "addl %1,%0"
				     :"=m"(value)
				     :"ir"(i), "m"(value));
	}

	inline void sub(int i) {
		__asm__ __volatile__(LOCK_PREFIX "subl %1,%0"
				     :"=m"(value)
				     :"ir"(i), "m"(value));
	}

	inline void inc(void) {
		__asm__ __volatile__(LOCK_PREFIX "incl %0"
				     :"=m"(value)
				     :"m"(value));
	}

	inline void dec(void) {
		__asm__ __volatile__(LOCK_PREFIX "decl %0"
				     :"=m"(value)
				     :"m"(value));
	}

private:
	volatile int value;
};

#endif	/* !_ATOMIC_INT_H_ */
