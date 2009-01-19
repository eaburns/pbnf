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
typedef unsigned long fp_type;

#define fp_sqrt2 1414
#define fp_one 1000
#define fp_infinity (numeric_limits<fp_type>::max())
