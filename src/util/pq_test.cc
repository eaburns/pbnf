/**
 * \file pq_test.c
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-02-11
 */

#include "priority_queue.h"

#include <iostream>

using namespace std;

class Int {
public:
	class IntCmp {
	public:
		int operator()(Int *a, Int *b)
		{
			return a->value - b->value;
		}
	};
	class IntSetInd {
	public:
		void operator()(Int *a, int ind)
		{
			a->index = ind;
		}
	};

	Int(int v) {
		value = v;
		index = -1;
	}

	int index;
	int value;
};

void print_heap(PriorityQueue<Int*, Int::IntCmp, Int::IntSetInd> pq)
{
	vector<Int*> v = pq.get_vec();

	for (unsigned int i = 0; i < v.size(); i += 1)
		cout << "[" << v[i]->value << "]";
	cout << endl;
}

int main(void)
{
	PriorityQueue<Int*, Int::IntCmp, Int::IntSetInd> pq;
	Int *one = new Int(1);

	pq.add(one);
	pq.add(new Int(2));
	pq.add(new Int(3));
	pq.add(new Int(4));
	pq.add(new Int(5));

	cout << "peek: " << pq.peek()->value << endl;
	delete pq.take();
	cout << "peek: " << pq.peek()->value << endl;

	one->value = 100;
	pq.elem_improved(one->index);
	cout << "peek: " << pq.peek()->value << endl;
	delete pq.take();
	cout << "peek: " << pq.peek()->value << endl;

	return 0;
}
