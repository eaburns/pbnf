/**
 * \file tiles_read_test.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#include <stdlib.h>

#include <iostream>

#include "tiles.h"

using namespace std;

int main(void)
{
	Tiles t(cin);

	t.print(cout);

	return EXIT_SUCCESS;
}
