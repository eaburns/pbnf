#ifdef USE_PRAGMA_IDENT_SRC
#pragma ident "@(#)symbolTable.cpp	1.66 06/11/30 12:20:27 JVM"
#endif
/*
 * @(#)symbolTable.cpp	1.66 06/11/30
 * 
 * Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
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
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 *  
 */

# include "incls/_precompiled.incl"
# include "incls/_symbolTable.cpp.incl"

// --------------------------------------------------------------------------

SymbolTable* SymbolTable::_the_table = NULL;

// Lookup a symbol in a bucket.

symbolOop SymbolTable::lookup(int index, const char* name,
                              int len, unsigned int hash) {
  for (HashtableEntry* e = bucket(index); e != NULL; e = e->next()) {
    if (e->hash() == hash) {
      symbolOop sym = symbolOop(e->literal());
      if (sym->equals(name, len)) {
        return sym;
      }
    }
  }
  return NULL;
}


// We take care not to be blocking while holding the
// SymbolTable_lock. Otherwise, the system might deadlock, since the
// symboltable is used during compilation (VM_thread) The lock free
// synchronization is simplified by the fact that we do not delete
// entries in the symbol table during normal execution (only during
// safepoints).

symbolOop SymbolTable::lookup(const char* name, int len, TRAPS) {  
  unsigned int hashValue = hash_symbol(name, len);
  int index = the_table()->hash_to_index(hashValue);

  symbolOop s = the_table()->lookup(index, name, len, hashValue);

  // Found
  if (s != NULL) return s;
  
  // Otherwise, add to symbol to table
  return the_table()->basic_add(index, (u1*)name, len, hashValue, CHECK_NULL);
}

symbolOop SymbolTable::lookup(symbolHandle sym, int begin, int end, TRAPS) {
  char* buffer;
  int index, len;
  unsigned int hashValue;
  char* name;
  {
    debug_only(No_Safepoint_Verifier nsv;)

    name = (char*)sym->base() + begin;
    len = end - begin;
    hashValue = hash_symbol(name, len);
    index = the_table()->hash_to_index(hashValue);
    symbolOop s = the_table()->lookup(index, name, len, hashValue);
  
    // Found
    if (s != NULL) return s;
  }
   
  // Otherwise, add to symbol to table. Copy to a C string first.
  char stack_buf[128];
  ResourceMark rm(THREAD);
  if (len <= 128) {
    buffer = stack_buf;
  } else {
    buffer = NEW_RESOURCE_ARRAY_IN_THREAD(THREAD, char, len);
  }
  for (int i=0; i<len; i++) {
    buffer[i] = name[i];
  }
  // Make sure there is no safepoint in the code above since name can't move.
  // We can't include the code in No_Safepoint_Verifier because of the
  // ResourceMark.

  return the_table()->basic_add(index, (u1*)buffer, len, hashValue, CHECK_NULL);
}

symbolOop SymbolTable::lookup_only(const char* name, int len,
                                   unsigned int& hash) {  
  hash = hash_symbol(name, len);
  int index = the_table()->hash_to_index(hash);

  return the_table()->lookup(index, name, len, hash);
}

void SymbolTable::add(constantPoolHandle cp, int names_count,
                      const char** names, int* lengths, int* cp_indices,
                      unsigned int* hashValues, TRAPS) {
  SymbolTable* table = the_table();
  bool added = table->basic_add(cp, names_count, names, lengths,
                                cp_indices, hashValues, CHECK);
  if (!added) {
    // do it the hard way
    for (int i=0; i<names_count; i++) {
      int index = table->hash_to_index(hashValues[i]);
      symbolOop sym = table->basic_add(index, (u1*)names[i], lengths[i],
                                       hashValues[i], CHECK);
      cp->symbol_at_put(cp_indices[i], sym);
    }
  }
}

// Needed for preloading classes in signatures when compiling.

symbolOop SymbolTable::probe(const char* name, int len) {
  unsigned int hashValue = hash_symbol(name, len);
  int index = the_table()->hash_to_index(hashValue);
  return the_table()->lookup(index, name, len, hashValue);
}


symbolOop SymbolTable::basic_add(int index, u1 *name, int len,
                                 unsigned int hashValue, TRAPS) {  
  assert(!Universe::heap()->is_in_reserved(name) || GC_locker::is_active(),
         "proposed name of symbol must be stable");

  // We assume that lookup() has been called already, that it failed,
  // and symbol was not found.  We create the symbol here.
  symbolKlass* sk  = (symbolKlass*) Universe::symbolKlassObj()->klass_part();
  symbolOop s_oop = sk->allocate_symbol(name, len, CHECK_NULL);
  symbolHandle sym (THREAD, s_oop);

  // Allocation must be done before grapping the SymbolTable_lock lock
  MutexLocker ml(SymbolTable_lock, THREAD);

  assert(sym->equals((char*)name, len), "symbol must be properly initialized");

  // Since look-up was done lock-free, we need to check if another
  // thread beat us in the race to insert the symbol.

  symbolOop test = lookup(index, (char*)name, len, hashValue);
  if (test != NULL) {
    // A race occured and another thread introduced the symbol, this one
    // will be dropped and collected.
    return test;
  }  

  HashtableEntry* entry = new_entry(hashValue, sym());
  add_entry(index, entry);
  return sym();
}

bool SymbolTable::basic_add(constantPoolHandle cp, int names_count,
                            const char** names, int* lengths,
                            int* cp_indices, unsigned int* hashValues,
                            TRAPS) {
  symbolKlass* sk  = (symbolKlass*) Universe::symbolKlassObj()->klass_part();
  symbolOop sym_oops[symbol_alloc_batch_size];
  bool allocated = sk->allocate_symbols(names_count, names, lengths,
                                        sym_oops, CHECK_false);
  if (!allocated) {
    return false;
  }
  symbolHandle syms[symbol_alloc_batch_size];
  int i;
  for (i=0; i<names_count; i++) {
    syms[i] = symbolHandle(THREAD, sym_oops[i]);
  }

  // Allocation must be done before grabbing the SymbolTable_lock lock
  MutexLocker ml(SymbolTable_lock, THREAD);

  for (i=0; i<names_count; i++) {
    assert(syms[i]->equals(names[i], lengths[i]), "symbol must be properly initialized");
    // Since look-up was done lock-free, we need to check if another
    // thread beat us in the race to insert the symbol.
    int index = hash_to_index(hashValues[i]);
    symbolOop test = lookup(index, names[i], lengths[i], hashValues[i]);
    if (test != NULL) {
      // A race occured and another thread introduced the symbol, this one
      // will be dropped and collected. Use test instead.
      cp->symbol_at_put(cp_indices[i], test);
    } else {
      symbolOop sym = syms[i]();
      HashtableEntry* entry = new_entry(hashValues[i], sym);
      add_entry(index, entry);
      cp->symbol_at_put(cp_indices[i], sym);
    }
  }

  return true;
}


void SymbolTable::verify() {
  for (int i = 0; i < the_table()->table_size(); ++i) {
    HashtableEntry* p = the_table()->bucket(i);
    for ( ; p != NULL; p = p->next()) {
      symbolOop s = symbolOop(p->literal());
      guarantee(s != NULL, "symbol is NULL");
#if DEBUG
      s->verify();
#endif
      guarantee(s->is_perm(), "symbol not in permspace");
      unsigned int h = hash_symbol((char*)s->bytes(), s->utf8_length());
      guarantee(p->hash() == h, "broken hash in symbol table entry");
      guarantee(the_table()->hash_to_index(h) == i,
                "wrong index in symbol table");
    }
  }
}


//---------------------------------------------------------------------------
// Non-product code

#ifndef PRODUCT

void SymbolTable::print_histogram() {
  MutexLocker ml(SymbolTable_lock);
  const int results_length = 100;
  int results[results_length];
  int i,j;
  
  // initialize results to zero
  for (j = 0; j < results_length; j++) {
    results[j] = 0;
  }

  int total = 0;
  int max_symbols = 0;
  int out_of_range = 0;
  for (i = 0; i < the_table()->table_size(); i++) {
    HashtableEntry* p = the_table()->bucket(i);
    for ( ; p != NULL; p = p->next()) {
      int counter = symbolOop(p->literal())->utf8_length();
      total += counter;
      if (counter < results_length) {
        results[counter]++;
      } else {
        out_of_range++;
      }
      max_symbols = MAX2(max_symbols, counter);
    }
  }
  tty->print_cr("Symbol Table:");
  tty->print_cr("%8s %5d", "Total  ", total);
  tty->print_cr("%8s %5d", "Maximum", max_symbols);
  tty->print_cr("%8s %3.2f", "Average",
	  ((float) total / (float) the_table()->table_size()));
  tty->print_cr("%s", "Histogram:");
  tty->print_cr(" %s %29s", "Length", "Number chains that length");
  for (i = 0; i < results_length; i++) {
    if (results[i] > 0) {
      tty->print_cr("%6d %10d", i, results[i]);
    }
  }
  int line_length = 70;    
  tty->print_cr("%s %30s", " Length", "Number chains that length");
  for (i = 0; i < results_length; i++) {
    if (results[i] > 0) {
      tty->print("%4d", i);
      for (j = 0; (j < results[i]) && (j < line_length);  j++) {
        tty->print("%1s", "*");
      }
      if (j == line_length) {
        tty->print("%1s", "+");
      }
      tty->cr();
    }
  }  
  tty->print_cr(" %s %d: %d\n", "Number chains longer than",
	            results_length, out_of_range);
}

#endif // PRODUCT

// --------------------------------------------------------------------------

#ifdef ASSERT
class StableMemoryChecker : public StackObj {
  enum { _bufsize = wordSize*4 };

  address _region;
  jint    _size;
  u1      _save_buf[_bufsize];

  int sample(u1* save_buf) {
    if (_size <= _bufsize) {
      memcpy(save_buf, _region, _size);
      return _size;
    } else {
      // copy head and tail
      memcpy(&save_buf[0],          _region,                      _bufsize/2);
      memcpy(&save_buf[_bufsize/2], _region + _size - _bufsize/2, _bufsize/2);
      return (_bufsize/2)*2;
    }
  }

 public:
  StableMemoryChecker(const void* region, jint size) {
    _region = (address) region;
    _size   = size;
    sample(_save_buf);
  }

  bool verify() {
    u1 check_buf[sizeof(_save_buf)];
    int check_size = sample(check_buf);
    return (0 == memcmp(_save_buf, check_buf, check_size));
  }

  void set_region(const void* region) { _region = (address) region; }
};
#endif


// --------------------------------------------------------------------------


// Compute the hash value for a java.lang.String object which would
// contain the characters passed in. This hash value is used for at
// least two purposes.
//
// (a) As the hash value used by the StringTable for bucket selection
//     and comparison (stored in the HashtableEntry structures).  This
//     is used in the String.intern() method.
//
// (b) As the hash value used by the String object itself, in
//     String.hashCode().  This value is normally calculate in Java code
//     in the String.hashCode method(), but is precomputed for String
//     objects in the shared archive file.
//
//     For this reason, THIS ALGORITHM MUST MATCH String.hashCode().

int StringTable::hash_string(jchar* s, int len) {
  unsigned h = 0;
  while (len-- > 0) {
    h = 31*h + (unsigned) *s;
    s++;
  }
  return h;
}

StringTable* StringTable::_the_table = NULL;

/** TJF --- started modifying below here! */

/* I just made up this MAX_LOAD value; I have no clue what a good value would
 * be.  The table size will be doubled every time there is more than (size *
 * MAX_LOAD) values in the table. */
#define MAX_LOAD 4
Harris::List* StringTable::list = NULL;
jint StringTable::size = 0;
segment_t StringTable::segments[NUM_SEGMENTS];
jint StringTable::count = 0;

StringTable::StringTable()
           : Hashtable(initial_table_size, sizeof (HashtableEntry))
{
	size = 2; /* initial size is 2. */
}

StringTable::StringTable(HashtableBucket* t, int number_of_entries)
           : Hashtable(initial_table_size, sizeof (HashtableEntry), t,
                       number_of_entries)
{
	size = 2; /* initial size is 2. */
}

/** We set the highest order bit and then AND it with the bucket.  if we get
 * back a bit, we and it off and break out.  otherwise we shift the bit down
 * and try again.  this continues until we get through the entire word. */
unsigned int
StringTable::get_parent(unsigned int bucket)
{
	unsigned int i;
	unsigned int val_if_high_bit_is_set = 0x80000000;
	unsigned int parent;

	for(i=val_if_high_bit_is_set; i > 0; i = (i >> 1)) {
		if(bucket & i) {
			parent = bucket & (~i);
			goto done;
		}
	}
	/* nothing?  the parent of 0 is 0, I guess... */
	parent = 0;

done:

	assert(parent ? parent < bucket : true,
	       "The parent must always be smaller than the source bucket!");
#ifdef DEBUG_VERBOSE
	tf_logv("the parent of %u is %u", bucket, parent);
#endif
	return parent;
}

/** Accesses a bucket indirectly via the segment table. */
Harris::BucketNode *
StringTable::get_bucket(unsigned int bucket)
{
	unsigned int segment = bucket / SEGMENT_SIZE;

#ifdef DEBUG_VERBOSE
	tf_logv("bucket %u goes in segment %u", bucket, segment);
#endif
	assert(segment < NUM_SEGMENTS, "Need to increase the number of segments");

	if(this->segments[segment] == NULL) {
		return NULL;
	}
	/* Shalev has this returning &(expr)... ? */
	return this->segments[segment][bucket % SEGMENT_SIZE];
}

/** Creates / sets a bucket indirectly via the segment table, creating a new
* segment if necessary. */
void
StringTable::set_bucket(unsigned int bucket, Harris::BucketNode *head)
{
	unsigned int segment = bucket / SEGMENT_SIZE;
	assert(segment < NUM_SEGMENTS, "Need to increase the number of segments");

	if(this->segments[segment] == NULL) {
		unsigned int i;
		segment_t new_segment;
		new_segment = new Harris::BucketNode*[SEGMENT_SIZE];
		/* all bucket ptrs in the segment start out uninitialized */
		for(i=0; i < SEGMENT_SIZE; ++i) {
			new_segment[i] = NULL;
		}
		if(!this->CAS((Harris::BucketNode**)&this->segments[segment], NULL,
		   (Harris::BucketNode*)new_segment)) {
			/* Another thread beat us to initializing the segment. */
			delete [] new_segment;
		}
	}
	this->segments[segment][bucket % SEGMENT_SIZE] = head;
}

/** Similar deal to Harris::List::CAS -- perform an atomic compare and swap,
 * taking arguments in the same order as Shalev's paper uses the operation.
 * @todo There should really just be one CAS implementation... */
bool
StringTable::CAS(Harris::BucketNode **think, Harris::BucketNode *old,
                 Harris::BucketNode *n_ptr)
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

	/** a CAS used for integers, so that we can double the size of the table. */
bool
StringTable::CAS(jint *word, jint old, jint new_val)
{
	jint existing = *word;

	Atomic::cmpxchg(new_val, word, old);
	if(*word == existing) {
		return true;
	}
	return false;
}

/** atomic increment of the given integer, for incrementing the count of the
 * number of elements in the table. */
jint
StringTable::fetch_and_inc(jint *w)
{
	Atomic::inc(w);
	return *w;
}

/** Initializes a bucket by searching fro where its pointer should be from
 * the parent bucket. */
void
StringTable::initialize_bucket(unsigned int bucket)
{
	unsigned int parent;
	Harris::BucketNode *b_parent;
	Harris::BucketNode *bckt = this->get_bucket(bucket);

	assert(bckt == NULL, "This bucket is already initialized!");
#ifdef DEBUG_VERBOSE
	tf_logv("Initializing bucket %u", bucket);
#endif

	parent = this->get_parent(bucket);
	b_parent = this->get_bucket(parent);
	if(b_parent == NULL) {
		this->initialize_bucket(parent);
		b_parent = this->get_bucket(parent);
	}
	assert(b_parent != NULL, "Bucket must be initialized by now!");

	Harris::BucketNode *dummy = new Harris::BucketNode(so_dummykey(bucket));
	if(!this->list->insert_at(b_parent, dummy)) {
		delete dummy;
		return;
	}
#ifdef DEBUG
	assert(this->list->find_bucket(b_parent, dummy),
	       "Bucket just inserted cannot be found from its parent!");
#endif
	this->set_bucket(bucket, dummy);
}

/** through the magic of `fortune'...
 * ``C code which reverses the bits in a word.'' */
#define REVERSE(n)                                          \
	n = ((n >>  1) & 0x55555555) | ((n <<  1) & 0xaaaaaaaa); \
	n = ((n >>  2) & 0x33333333) | ((n <<  2) & 0xcccccccc); \
	n = ((n >>  4) & 0x0f0f0f0f) | ((n <<  4) & 0xf0f0f0f0); \
	n = ((n >>  8) & 0x00ff00ff) | ((n <<  8) & 0xff00ff00); \
	n = ((n >> 16) & 0x0000ffff) | ((n << 16) & 0xffff0000);

/** sets the high order bit and then reverses the word.  Almost exactly as
 * implemented in the Shalev paper. */
juint StringTable::so_regularkey(juint key)
{
	int ret = key | 0x80000000;
	REVERSE(ret);
	return ret;
}

/** reverses the bits in the word */
juint StringTable::so_dummykey(juint key)
{
	juint ret = key;
	REVERSE(ret);
	return ret;
}

oop StringTable::basic_add(Handle string_or_null, jchar* name, int len, TRAPS)
{
	debug_only(StableMemoryChecker smc(name, len * sizeof(name[0])));
	assert(!Universe::heap()->is_in_reserved(name) || GC_locker::is_active(),
	       "proposed name of symbol must be stable");

	Handle string;
	// try to reuse the string if possible
	if (!string_or_null.is_null() && string_or_null()->is_perm()) {
		string = string_or_null;
	} else {
		string = java_lang_String::create_tenured_from_unicode(name, len,
		                                                       CHECK_NULL);
	}

	assert(java_lang_String::equals(string(), name, len),
	      "string must be properly initialized");
#ifdef DEBUG_VERBOSE
	if(!string()->is_symbol()) {
		ResourceMark rm;
		tf_logv("Interning non-symbol oop at %p, %s(%d)", string(),
		        UNICODE::as_utf8(name, len), len);
	}
#endif

	juint key = StringTable::hash_string(name, len);
	/* note: Handles are silly; they overload `()' to get the oop they hold. */
	Harris::Node *node = new Harris::Node(name, len, so_regularkey(key),
	                                      string());
	unsigned int bucket = key % this->size;

	Harris::BucketNode *bn = this->get_bucket(bucket);

	if(bn == NULL) {
		this->initialize_bucket(bucket);
		bn = this->get_bucket(bucket);
	}
	assert(bn != NULL, "initialize_bucket must have failed!");
	assert(bn->next != NULL, "How can the bucket not have a next pointer?!");

	if(!this->list->insert_at(bn, node)) { /* Insert happens here */
#ifdef DEBUG
		tf_log("Node is already in the list!");
#endif
		delete node;
		return string();
	}

	jint local_size = size;
	if((this->fetch_and_inc(&this->count) / local_size) > MAX_LOAD) {
#ifdef DEBUG
		tf_logv("expanding table from %d to %d", local_size, 2 * local_size);
#endif
		this->CAS(&this->size, local_size, 2 * local_size);
	}
	assert(this->size <= (NUM_SEGMENTS * SEGMENT_SIZE), "Table is too large.");
		
#ifdef DEBUG_VERBOSE
	this->list->print(bn);
#endif

#ifdef DEBUG
	oop search_result;

#ifdef DEBUG_VERBOSE
	tf_log("Oop we just inserted should be reachable from the head:");
#endif
	assert(this->list->in_list(node),
	       "Head-based search did not find newly inserted element.");
#ifdef DEBUG_VERBOSE
	tf_logv("Oop we just inserted should be reachable from bucket %u:", bucket);
#endif
	assert(StringTable::the_list()->find(bn, node->key, &search_result),
	       "bucket-based search did not find the new element.");
	assert(search_result != NULL, "find reported success but found nothing!");

	this->verify();
	return search_result;
#else
	return string();
#endif /* DEBUG */
}

/** public lookup method */
oop StringTable::lookup(symbolOop symbol) {
	int length;
	jchar* chars = symbol->as_unicode(length);

	return StringTable::lookup(chars, length);
}

/** internal lookup method */
oop StringTable::lookup(jchar *chars, int length) {
	oop o;
	unsigned int bucket;
	juint key = StringTable::hash_string(chars, length);

	key = StringTable::hash_string(chars, length);
	bucket = key % the_table()->size;

	/* We need to keep searching for a bucket until we find one.
	 * Picture key 't', which belongs in bucket 'n'.  However 'n' is not
	 * initialized -- thus we should find 't' from bucket 'm'.  'm' might not be
	 * initialized either -- we have to keep going back, all the way to 'a'.
	 * We are guaranteed that a bucket will be found somewhere in the chain
	 * because bucket 0 ('a') is always initialized. */
	Harris::BucketNode *bn = NULL;
	do {
		bn = the_table()->get_bucket(bucket);
		bucket = the_table()->get_parent(bucket);
	} while(bn == NULL);

	the_list()->find(bn, StringTable::so_regularkey(key), &o);
	return o;
}

oop StringTable::intern(Handle string_or_null, jchar* name,
                        int len, TRAPS) {
	oop string;

	string = the_table()->lookup(name, len);

	if(string != NULL) {
		return string;
	}
#ifdef DEBUG_VERBOSE
	ResourceMark rm;
	tf_logv("Interning \"%s\"", UNICODE::as_utf8(name, len));
#endif
	return the_table()->basic_add(string_or_null, name, len, CHECK_NULL);
}

oop StringTable::intern(symbolOop symbol, TRAPS) {
  if (symbol == NULL) return NULL;
  ResourceMark rm(THREAD);
  int length;
  jchar* chars = symbol->as_unicode(length);
  Handle string;
  oop result = intern(string, chars, length, CHECK_NULL);
  return result;
}


oop StringTable::intern(oop string, TRAPS)
{
  if (string == NULL) return NULL;
  ResourceMark rm(THREAD);
  int length;
  Handle h_string (THREAD, string);
  jchar* chars = java_lang_String::as_unicode_string(string, length);
  oop result = intern(h_string, chars, length, CHECK_NULL);
  return result;
}


oop StringTable::intern(const char* utf8_string, TRAPS) {
  if (utf8_string == NULL) return NULL;
  ResourceMark rm(THREAD);
  Handle string;
  int length = UTF8::unicode_length(utf8_string);
  jchar* chars = NEW_RESOURCE_ARRAY(jchar, length);

  UTF8::convert_to_unicode(utf8_string, chars, length);

  oop result = intern(string, chars, length, CHECK_NULL);
  return result;
}

void StringTable::verify() {
#ifdef DEBUG
	unsigned int segment, i;
	assert(size > 0, "Must be able to have *something* in the table.");
	assert(segments[0] != NULL,
	       "Since bucket 0 is initialized on creation, the 0th segment should "
	       "always be initialized!");
	for(segment=0; segment < NUM_SEGMENTS; segment++) {
		if(the_table()->segments[segment]) {
			for(i=1; i < SEGMENT_SIZE-1; ++i) {
				Harris::BucketNode *cur = the_table()->segments[segment][i];

				if(cur) {
					Harris::BucketNode *b_parent;
					juint parent;
					parent = cur->key;
					REVERSE(parent);
					parent = the_table()->get_parent(parent);
					b_parent = the_table()->get_bucket(parent);
					assert(b_parent, "Bucket has no parent?!");
					assert(b_parent->key < cur->key, "Buckets not ordered");
				}
			}
		}
	}
#endif
}
