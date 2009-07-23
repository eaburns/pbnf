/**
 * \file thread_specific.h
 *
 * A thread specific type.
 *
 * \author eaburns
 * \date 2009-07-23
 */

#if !defined(_THREAD_SPECIFIC_H_)
#define _THREAD_SPECIFIC_H_

#include <vector>
using namespace std;

#include "thread.h"

/* To attempt to prevent cache ping-ponging? */
#define PADDING 24 		/* bytes */

template <class T>
class ThreadSpecific {
private:
	/* Ensure that the array is large enough for [tid] number of
	 * elements. */
	void ensure_size(unsigned int tid)
	{
		if (tid >= entries.size()) {
			struct padded_entry ent;
			ent.data = init_val;
			entries.resize(tid + 1, ent);
		}

	}
public:
	ThreadSpecific(T iv)
	{
		init_val = iv;
	}

	T get_value(void)
	{
		unsigned int tid = Thread::current()->get_id();
		ensure_size(tid);
		return entries[tid].data;
	}

	void set_value(T v)
	{
		unsigned int tid = Thread::current()->get_id();
		ensure_size(tid);
		entries[tid].data = v;
	}

	/**
	 * Get all entries.
	 */
	vector<T> get_all_entries(void)
	{
		typename vector<struct padded_entry>::iterator iter;
		vector<T> ret;

		for (iter = entries.begin(); iter != entries.end(); iter++)
			ret.push_back((*iter).data);

		return ret;
	}

private:
	T init_val;

	/* We want to try to get each element of the array on a
	 * seperate cache line. */
	struct padded_entry {
		T data;
		char padding[PADDING];
	};

	vector<struct padded_entry> entries;
};

#endif	/* !_THREAD_SPECIFIC_H_ */
