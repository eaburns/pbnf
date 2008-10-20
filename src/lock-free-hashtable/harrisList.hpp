/*
 * @(#)harrisList.hpp	1.45 06/11/30
 * 
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *   
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *  
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *   
 */
/** This is an implementation of Harris' non-blocking algorithm for the
 * implementation of a linked list.  For more information, see ``A Pragmatic
 * Implementation of Non-Blocking Linked Lists'', Timothy L. Harris,
 * University of Cambridge Computer Laboratory, Cambridge, UK.
 * (I found the paper via his website @ microsoft) */

namespace Harris {

/** A single node in the list. */
class Node: public CHeapObj {
	public:
		Node(jchar *nm, int length, juint key, oop o_p);

		virtual bool is_sentinel() const;

	public:
		oop o;
		jchar *name;
		int len;
		juint key;
		class Node *next;

	private:
		Node();
		Node(jchar *, int);
		Node& operator = (const Node &);
};

class SentinelNode: public Node {
	public:
		/** SentinelNodes need the bucket index to construct a dummy key */
		SentinelNode(juint key);

		virtual bool is_sentinel() const;

	protected:

	private:
		/* These shouldn't be used -- don't make sense for a sentinel node. */
		SentinelNode();
		SentinelNode(jchar *name, int length);
		SentinelNode(jchar *name, int length, oop o);
		SentinelNode& operator = (const SentinelNode &);
};

/* A bucket node is essentially the head of one list (and potentially the tail
 * of another).  Thus it forms a kind of sentinel. */
class BucketNode: public SentinelNode {
	public:
		BucketNode(juint key);
		virtual bool is_sentinel() const;
	private:
		/* These shouldn't be used -- bucket nodes hold no data */
		BucketNode();
		BucketNode(jchar *name, int length);
		BucketNode(jchar *name, int length, oop o);
		BucketNode& operator = (const BucketNode &);
};


/** The actual list implementation */
class List {
	public:
		List();
		~List();

		bool insert(Node *);
		/* inserts somewhere between the first argument and the next Sentinel in
		 * the list. */
		bool insert_at(SentinelNode *start, Node *);

		/** searches for the given element starting from a particular location
		 * in the list. */
		bool find(SentinelNode *start, juint search_key, oop *);

#ifdef DEBUG
		/** searches just for a bucket, thus skips over sentinel nodes. */
		bool find_bucket(SentinelNode *start, BucketNode *);

		/** makes sure our list is valid. */
		void verify();

		/** asserts properties on individual buckets, such as the allowable key
		 * values. */
		void verify_bucket(SentinelNode *);

		/** prints every element from the given node until a sentinel node. */
		void print(const Node *start);

		/** searches from the head to make sure the given element got into the
		 * list. */
		bool in_list(const Node *);
#endif /* DEBUG */

		/** The hash table needs to initialize its first element to the head of
		 * this list */
		BucketNode *get_head();

	protected:
		/** returns the number of elements in the list */
		unsigned int length();

	private:
		/* searches the list beginning at the given start node. */
		Node *search(SentinelNode *start, juint search_key, Node **left);

		/** performs a CAS like expected in the Harris paper -- we give what
		 * we think the pointer should be (what it will be if no other thread
		 * jumped in on us), what it *is* now, and what we want it to become
		 * if it hasn't changed. */
		bool CAS(Node **think, Node *old, Node *n_ptr);

		/** returns whether or not a node is marked. */
		bool marked(const void * const word);

		/** derives an unmarked reference from a marked one. */
		Node *get_unmarked(const void * const word);

	private:
		BucketNode *head, *tail;
}; /* class List */

}; /* namespace Harris */
