/**
 * \file fixed_point.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-01-16
 */

#include "stdint.h"

#include <limits>

/* The type of a fixed point value.  This should never be larger than
 * the size of the type for the 'value' field in the AtomicInt
 * class. */
/*
typedef double fp_type;

#define fp_sqrt2 1.41421356237
#define fp_one 1.0
#define fp_infinity (numeric_limits<double>::infinity())
*/
typedef uint64_t fp_type;

#define fp_sqrt2 14142
#define fp_one 10000
#define fp_infinity (numeric_limits<fp_type>::max())
