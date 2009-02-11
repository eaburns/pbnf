/**
 * \file pq.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-02-10
 */

#include <assert.h>

#include <iostream>
#include <vector>

/**
 * A template priority queue class.
 */
template<class Elem, class ElemCmp, class ElemSetInd> class PriorityQueue {
public:

	void add(Elem e);
	Elem take(void);
	Elem peek(void);
	bool empty(void);

	/** When the value of an element gets better (closer to the
	 * front of the queue) this function re-sifts it. */
	void elem_improved(int i);

	std::vector<Elem> get_vec(void) { return heap; }

private:
	int left_of(int i);
	int right_of(int i);
	int parent_of(int i);
	int is_leaf(int i);
	int max_child(int i);
	void sift_up(int i);
	void sift_down(int i);

	int fill;
	std::vector<Elem> heap;
	ElemCmp cmp;
	ElemSetInd set_index;
};

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::left_of(int i)
{
	return 2 * i + 1;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::right_of(int i)
{
	return 2 * i + 2;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::parent_of(int i)
{
	return (i - 1) / 2;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::is_leaf(int i)
{
	return left_of(i) > fill && right_of(i) > fill;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::max_child(int i)
{
	int right = right_of(i);
	int left = left_of(i);
	assert(!is_leaf(i));
	if (left < fill && right < fill) {
		if (cmp(heap[right], heap[left]) > 0)
			return right;
		else
			return left;
	} else if (left < fill) {
		return left;
	} else {
		return right;
	}
	assert(1); /* Should never reach here. */
	return -1;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::sift_up(int i)
{
	if (i > 0) {
		int p_ind = parent_of(i);
		Elem elm = heap[i];
		Elem parent = heap[p_ind];
		if (cmp(elm, parent) > 0) {
			heap[i] = parent;
			set_index(parent, i);
			heap[p_ind] = elm;
			set_index(elm, p_ind);
			sift_up(p_ind);
		}
	}
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::sift_down(int i)
{
	if (!is_leaf(i)) {
		int max_c_ind = max_child(i);
		Elem elm = heap[i];
		Elem max_c = heap[max_c_ind];

		if (cmp(elm, max_c) < 0) {
			heap[i] = max_c;
			set_index(max_c, i);
			heap[max_c_ind] = elm;
			set_index(elm, max_c_ind);
			sift_down(max_c_ind);
		}
	}
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::add(Elem e)
{
	if (heap.size() > (unsigned int) fill)
		heap[fill] = e;
	else
		heap.push_back(e);

	sift_up(fill);
	fill += 1;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	Elem PriorityQueue<Elem, ElemCmp, ElemSetInd>::take(void)
{
	Elem head;

	if (fill <= 0)
		return NULL;

	head = heap[0];
	set_index(head, -1);

	fill -= 1;
	if (fill > 0) {
		heap[0] = heap[fill];
		set_index(heap[0], 0);
		sift_down(0);
	}

	return head;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	Elem PriorityQueue<Elem, ElemCmp, ElemSetInd>::peek(void)
{
	if (fill <= 0)
		return NULL;

	return heap[0];
}

template<class Elem, class ElemCmp, class ElemSetInd>
	bool PriorityQueue<Elem, ElemCmp, ElemSetInd>::empty(void)
{
	return fill <= 0;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::elem_improved(int i)
{
	sift_up(i);
}
