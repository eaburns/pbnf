/**
 * \file hashtbl.c
 *
 * A simple fixed size hash table using an array of lf_ordlist
 * buckets.
 *
 * \author eaburns
 * \date 2009-04-10
 */

#define _POSIX_C_SOURCE 200112L

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#include "lockfree.h"		/* for lf_ordlist */

struct lf_hashtbl {
	uint64_t (*hash)(void*);

	size_t nbuckets;
	struct lf_ordlist **buckets;
}

struct lf_hashtbl *lf_hashtbl_create(size_t nbrelm,
				     size_t nbuckets,
				     int (*cmp)(void *, void*),
				     uint64_t (*hash)(void*))
{
	int i;
	struct lf_hashtbl *tbl;

	tbl = calloc(1, sizeof(*tbl));
	if (!tbl)
		return NULL;
	tbl->nbuckets = nbuckets;
	tbl->hash = hash;
	tbl->buckets = calloc(nbuckets, sizeof(*tbl->buckets));
	if (!tbl->buckets)
		goto err_buckets;

	for (i = 0; i < nbuckets; i += 1) {
		tbl->buckets = lf_ordlist_create(nbrelm, cmp);
		if (!tbl->buckets)
			goto err_lists;
	}

	return tbl;

err_lists:
	for (i -= 1; i >= 0; i -= 1)
		lf_ordlist_destroy(tbl->buckets[i]);

err_buckets:
	free(tbl);
	return NULL;
}

void lf_hashtbl_destroy(struct lf_hashtbl *tbl)
{
	int i;

	for (i = 0; i < tbl->nbuckets; i += 1)
		lf_ordlist_destroy(tbl->buckets[i]);

	free(tbl->buckets);
	free(tbl);
}
