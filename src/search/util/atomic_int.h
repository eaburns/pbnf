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
	AtomicInt(unsigned int val) { value = val; }

	inline unsigned int read(void) const { return value; }

	inline void set(unsigned int i) { value = i; }

	inline void add(unsigned int i) {
		__asm__ __volatile__(LOCK_PREFIX "addl %1,%0"
				     :"=m"(value)
				     :"ir"(i), "m"(value));
	}

	inline void sub(unsigned int i) {
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

	inline unsigned int swap(unsigned int n) {
		__asm__ __volatile__("xchgl %0,%1"
				     : "=r" (n)
				     : "m" (value), "0" (n)
				     : "memory");

		return n;
	}

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
	inline unsigned int cmp_and_swap(unsigned int o, unsigned int n) {
		unsigned int prev;

		__asm__ __volatile__("cmpxchgl %1,%2"
				     : "=a"(prev)
				     : "r"(n), "m"(value), "0"(o)
				     : "memory");
		return prev;
	}

private:
	volatile unsigned int value;
};

#endif	/* !_ATOMIC_INT_H_ */
