/** This is an implementation of Harris' non-blocking algorithm for the
 * implementation of a linked list.  For more information, see ``A Pragmatic
 * Implementation of Non-Blocking Linked Lists'', Timothy L. Harris,
 * University of Cambridge Computer Laboratory, Cambridge, UK.
 * (I found the paper via his website @ microsoft) */
# include "incls/_precompiled.incl"
# include "incls/_harrisList.cpp.incl"

namespace Harris {

/** need to define some sort of key for the sentinel nodes `head' and `tail'.
 * We don't want this key to ever occur in the list though, as it could give us
 * a false indication that we're at the head / tail when we are in fact, not */
#define BAD_KEY ((juint)0xFFFFFFFF)

Node::Node(jchar *nm, int length, juint key, oop o_p) {
	this->o = o_p;
	if(nm) {
		/* make a copy of the jchar string. */
		this->name = NEW_C_HEAP_ARRAY(jchar, length);
		assert(this->name, "Memory allocation failed.");
		memcpy(this->name, nm, length * sizeof(jchar));
	} else {
		this->name = NULL;
	}
	this->len = length;
	this->key = key;
	this->next = NULL;
}
bool Node::is_sentinel() const { return false; }

/* A sentinel node is a node with a `dummy' key, in Shalev notation. */
SentinelNode::SentinelNode(juint key): Node(NULL, -1, BAD_KEY, NULL)
{
	this->o = NULL;
	this->name = NULL;
	this->len = -1;
	this->key = key;
	this->next = NULL;
}

bool SentinelNode::is_sentinel() const { return true; }
BucketNode::BucketNode(juint key): SentinelNode(key) { }
bool BucketNode::is_sentinel() const { return true; }

/** head and tail pointers always exist. */
List::List()
{
	this->head = new BucketNode(StringTable::so_dummykey(0));
	this->tail = new BucketNode(StringTable::so_dummykey(0x7FFFFFFF));
	/* Tried to do this with CHeapObj operator new allocation, but it didn't
	 * seem to call the constructor: */
	assert(this->head->len == (int)BAD_KEY,
	       "Wrong constructor was used creating SentinelNode");
	assert(this->tail->next == NULL, "Next pointer not initiliazed correctly.");
	this->head->next = this->tail;
}

List::~List()
{
	/** @todo garbage collected?  do I free memory I allocated myself?
	 * I assume CHeapObj memory is garbage collected, so I only delete what I
	 * have allocated via operator new() */
	delete this->head; 
	delete this->tail; 
}

/** insert method, (mostly) as Harris has it.  This operation does not return
 * until the node is in the list, whether it was inserted by the running thread
 * (return value: true) or another (return value: false).  The inserted node
 * will be after the given Sentinel, but before any other Sentinel in the list.
 */
bool
List::insert_at(SentinelNode *start, Node *new_node)
{
	Node *left, *right;

#ifdef DEBUG
	if(!new_node->is_sentinel()) {
		assert(new_node->key != BAD_KEY,
		       "Hash key is the special `sentinel' key!");
		assert(new_node->len > 0 ? new_node->name != NULL : true,
		       "Where's the string?");
	}
	assert(new_node->key > start->key, "Using the wrong bucket for insertion.");
	this->verify();
#endif

	do { /* infinite loop until something fails / works */
		right = this->search(start, new_node->key, &left);
#if 0
		if((!right->is_sentinel()) && (right->key == new_node->key)) {
#else
		if(left == NULL) {
#endif
			/* Already in the list -- perhaps another thread beat us to the
			 * insertion. */
			return false;
		}
		assert(new_node->key > left->key, "Insertion breaks key ordering");
		new_node->next = right;

		if(this->CAS(&(left->next), right, new_node)) {
			/* Can't do this assertion earlier -- we are basically asserting that
			 * we didn't find a double, but its perfectly reasonable to find a
			 * double -- another thread could beat us to the insertion.  However
			 * once we're here we know the insert was successful, so we shouldn't
			 * have doubles. */
			assert(right != NULL ? new_node->key < right->key : true,
			       "Insertion breaks key ordering");
			return true;
		}
	} while(true);
}

/** simply a forwarder to the other insert, with the `start'ing node being the
 * head node of this list. */
bool
List::insert(Node *new_node)
{
	this->insert_at(this->head, new_node);
}

/** searches for the given element starting from a particular location in the
 * list. */
bool
List::find(SentinelNode *start, juint search_key, oop *right_data)
{
	Node *left_node, *right_node;

#ifdef DEBUG
	this->verify();
	assert(this->in_list(start),
	       "Node is not in the list -- where did you get it?");
#endif

	*right_data = NULL;
	right_node = this->search(start, search_key, &left_node);
#if 0
	if((right_node->is_sentinel()) || (right_node->key != search_key)) {
#else
	if(right_node->key != search_key) {
#endif
		return false;
	} else {
		*right_data = right_node->o;
		return true;
	}
}

#ifdef DEBUG
/** searches just for a bucket, thus skips over sentinel nodes. */
bool
List::find_bucket(SentinelNode *start, BucketNode *bckt)
{
	Node *node;

	for(node = start; node && node->key <= bckt->key; node = node->next) {
		if(node == bckt) { return true; }
	}
	return false;
}
#endif

#ifdef DEBUG
/* makes sure our list is valid. */
void
List::verify()
{
	Node *node;

	assert(this->head, "Where did the head node go?!");
	assert(this->tail, "Where did the tail node go?!");
	for(node = this->head; node; node = node->next) {
		assert(node != node->next, "Infinite loop in list.");
		if(node->next && !node->is_sentinel() && !(node->next->is_sentinel())) {
			assert(node->key <= node->next->key, "List is not ordered.");
		}
		assert(node != tail && (node->key & 0x00000001) ? !node->is_sentinel() : 
		       true, "Bucket node has lower bit set!");
		if(node->is_sentinel()) {
			/* The tail is the only node which is allowed to have a NULL next
			 * pointer. */
			if(node != this->tail) {
				assert(node->next, "Non-data node with no next pointer.");
			}
			assert(node->len == (int)BAD_KEY, "Length should not be initialized");
			assert(node->name == NULL, "Sentinels do not hold data");
			assert(node->o == NULL, "Sentinels do not hold oops");
		} else {
			/* According to the original StringTable implementation, every oop
			 * in the table (e.g. this list) should be nonnull and in the
			 * permspace. */
			guarantee(node->o != NULL, "interned string is NULL");
			guarantee(node->o->is_perm(), "interned string not in permspace");
			assert(node->key & 0x00000001, "Lower bit must be set for data nodes!");

			/* of course, the hash stored in the node should match what would be
			 * computed based on the data. */
			int length;
			jchar *chars = java_lang_String::as_unicode_string(node->o, length);
			assert(node->key == StringTable::so_regularkey(
			                     StringTable::hash_string(chars, length)),
			       "broken hash in string table (Harris List)");
			assert(java_lang_String::equals(node->o, chars, length),
			       "broken string in string table");
		}
	}
}

#define TJF_UTF8_BUF_SZ 1024
/** VERBOSE print of every element in the list. */
void
List::print(const Node *start)
{
	const Node *node;
	char buf[TJF_UTF8_BUF_SZ];
	ResourceMark rm;

	for(node = start;
	    node && (node == start) ? true : !node->is_sentinel();
	    node = node->next) {
		if(node == this->head) {
			printf("(Head)");
		} else if (node == this->tail) {
			printf("(Tail)");
		} else if (node->is_sentinel()) {
			/* The key given also tells the bucket number.  Unfortunately it's
			 * bit-reversed, so just printing it out gives ridiculous numbers.  We
			 * need to bit-reverse it again to get the actual bucket number
			 * represented.
			 * so_dummykey() happens to do this, but this is bad.  Really
			 * REVERSE() should be defined such that both Harris::List AND
			 * StringTable have access to it.
			 * THIS WILL BREAK IF THE IMPLEMENTATION OF StringTable::so_dummykey()
			 * CHANGES! */
			printf("(Bucket %u)", StringTable::so_dummykey(node->key));
		} else {
			UNICODE::as_utf8(node->name, node->len, buf, TJF_UTF8_BUF_SZ);
			printf("%s", buf);
		}
		if(node->next && !(node->next->is_sentinel())) {
			printf(" -> ");
		}
	}
	puts("");
	fflush(stdout);
}
#endif /* DEBUG */

/** The hash table needs to initialize its first element to the head of
 * this list */
BucketNode *
List::get_head()
{
	return this->head;
}

/** returns the number of elements in the list */
unsigned int
List::length()
{
	Node *node;
	unsigned int count = 0;

#ifdef DEBUG
	this->verify();
#endif
	node = this->head;
	while(node) {
		count++;
		node = node->next;
	}
	return count;
}

/** searches for the node which matches the information.  returns the node
 * itself, and modifies the last argument to be the previous node. */
Node *
List::search(SentinelNode *start, juint search_key, Node **left)
{
	Node *left_node_next = NULL, *right_node = NULL;

#ifdef DEBUG
	this->verify();
	assert(start, "Node we are searching from must be a real node!");
#ifdef DEBUG_VERBOSE
	tf_logv("searching for key <%u> in %u element list", search_key,
	        this->length());
#endif /* DEBUG_VERBOSE */
#endif /* DEBUG */

	*left = start;
	Node *cur = start->next;

	while(1) {
		if(cur == NULL) { *left = NULL; return NULL; }
		/* doesn't matter if we hit another bucket -- just keep going until we
		 * hit the end of the list or a key that indicates we're done. */
		if(cur->key >= search_key) {
			return cur;
		}
		*left = cur;
		cur = cur->next;
	}
}

/** performs a CAS like expected in the  paper -- we give what we
 * think the pointer should be (what it will be if no other thread jumped
 * in on us), what it *is* now, and what we want it to become if it
 * hasn't changed.
 * The argument order is designed to match that given in the  paper. */
bool
List::CAS(Node **think, Node *old, Node *n_ptr)
{
	void *ptr = (void*)*think;
	assert(n_ptr != NULL, "Are you sure you want to swap in a NULL pointer?");
	/* do a compare and swap -- if the `*think' pointer changes, then we know it
	 * succeeded. */
	Atomic::cmpxchg_ptr((void*)n_ptr, (void*)think, (void*)old);
	if(ptr != *think) {
		return true;
	}
	return false;
}

/** a node is marked if the pointer to it has its low order bit set. */
bool
List::marked(const void * const word)
{
	/* intptr_t -- should give the same word size as void* on both 32 and 64 bit
	 * archictectures.  hopefully... */
	if((void*) (((intptr_t)word) & ((int)0x00000001L))) {
		tf_log("!!! Actually found a marked node!");
	}
	return ((void*) (((intptr_t)word) & ((int)0x00000001L)));
}

/** a node is unmarked by unsetting its low order bit. */
Node *
List::get_unmarked(const void * const word)
{
	return ((Node*) (((intptr_t)word) & ((int)0xFFFFFFFE)));
}

#ifdef DEBUG
/** @return whether or not the given node is in this list. */
bool
List::in_list(const Node *search)
{
	Node *node;

	for(node = this->head; node; node = node->next) {
		if(node == search) {
			return true;
		}
	}
	return false;
}
#endif /* DEBUG */

}; /* namespace Harris */
