#ifdef USE_PRAGMA_IDENT_HDR
#pragma ident "@(#)symbolTable.hpp	1.45 06/11/30 12:20:27 JVM"
#endif
/*
 * @(#)symbolTable.hpp	1.45 06/11/30
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

// The symbol table holds all symbolOops and corresponding interned strings.
// symbolOops and literal strings should be canonicalized.
//
// The interned strings are created lazily.
//
// It is implemented as an open hash table with a fixed number of buckets.
//
// %note:
//  - symbolTableEntrys are allocated in blocks to reduce the space overhead.
#include "tf_err.h"

class BoolObjectClosure;


class SymbolTable : public Hashtable {
  friend class VMStructs;

private:
  // The symbol table
  static SymbolTable* _the_table;

  // Adding elements    
  symbolOop basic_add(int index, u1* name, int len,
                      unsigned int hashValue, TRAPS);
  bool basic_add(constantPoolHandle cp, int names_count,
                 const char** names, int* lengths, int* cp_indices,
                 unsigned int* hashValues, TRAPS);

  // Table size
  enum {
    symbol_table_size = 20011
  };

  symbolOop lookup(int index, const char* name, int len, unsigned int hash);

  SymbolTable()
    : Hashtable(symbol_table_size, sizeof (HashtableEntry)) {}

  SymbolTable(HashtableBucket* t, int number_of_entries)
    : Hashtable(symbol_table_size, sizeof (HashtableEntry), t,
                number_of_entries) {}


public:
  enum {
    symbol_alloc_batch_size = 8
  };

  // The symbol table
  static SymbolTable* the_table() { return _the_table; }

  static void create_table() {
    assert(_the_table == NULL, "One symbol table allowed.");
    _the_table = new SymbolTable();
  }

  static void create_table(HashtableBucket* t, int length,
                           int number_of_entries) {
    assert(_the_table == NULL, "One symbol table allowed.");
    assert(length == symbol_table_size * sizeof(HashtableBucket),
           "bad shared symbol size.");
    _the_table = new SymbolTable(t, number_of_entries);
  }

  static symbolOop lookup(const char* name, int len, TRAPS);
  // lookup only, won't add. Also calculate hash.
  static symbolOop lookup_only(const char* name, int len, unsigned int& hash);
  // Only copy to C string to be added if lookup failed.
  static symbolOop lookup(symbolHandle sym, int begin, int end, TRAPS);

  static void add(constantPoolHandle cp, int names_count,
                  const char** names, int* lengths, int* cp_indices,
                  unsigned int* hashValues, TRAPS);

  // GC support
  //   Delete pointers to otherwise-unreachable objects.
  static void unlink(BoolObjectClosure* cl) {
    the_table()->Hashtable::unlink(cl);
  }

  // Invoke "f->do_oop" on the locations of all oops in the table.
  static void oops_do(OopClosure* f) {
    the_table()->Hashtable::oops_do(f);
  }

  // Symbol lookup
  static symbolOop lookup(int index, const char* name, int len, TRAPS);

  // Needed for preloading classes in signatures when compiling.
  // Returns the symbol is already present in symbol table, otherwise
  // NULL.  NO ALLOCATION IS GUARANTEED!
  static symbolOop probe(const char* name, int len);

  // Histogram
  static void print_histogram()     PRODUCT_RETURN;

  // Debugging
  static void verify();

  // Sharing
  static void copy_buckets(char** top, char*end) {
    the_table()->Hashtable::copy_buckets(top, end);
  }
  static void copy_table(char** top, char*end) {
    the_table()->Hashtable::copy_table(top, end);
  }
  static void reverse(void* boundary = NULL) {
    ((Hashtable*)the_table())->reverse(boundary);
  }
};


/** Size of the segment table.  This determines the number of buckets we can
 * have as a max; 256*1024 == 262144. */
#define NUM_SEGMENTS 256
#define SEGMENT_SIZE 1024
/* should be BN* segment_t[SEGMENT_SIZE], but using array types is a real pain
 * when everything is using dynamic memory. */
typedef Harris::BucketNode** segment_t;

class StringTable : public Hashtable {
  friend class VMStructs;

private:
	/* The string table -- singleton */
	static StringTable* _the_table;
	static Harris::List* list;
	/** total size of the table, always a power of 2.  This should really be an
	 * unsigned int but it needs to be a jint because there is no atomic
	 * increment code in the JVM source for unsigned integers (and I did not
	 * feel like writing one myself). */
	static jint size;
	/** segment table, layer of indirection for hash table so we don't have to
	 * have a lock to copy pointers from one table to another. */
	static segment_t segments[NUM_SEGMENTS];
	static jint count; /**< number of elements in the table */

  static oop intern(Handle string_or_null, jchar* chars, int length, TRAPS);
  oop basic_add(Handle string_or_null, jchar* name, int len, TRAPS);

	// Table size
	enum {
		initial_table_size = 2
	};

	/** constructs a table of size 2. */
	StringTable();

	/** Not sure what this did originally.  Constructs the parent object as
	 * it used to, but constructs this object as in the default constructor,
	 * ignoring arguments. */
	StringTable(HashtableBucket* t, int number_of_entries);

	/** unsets the most significant turned-on bit. */
	unsigned int get_parent(unsigned int);

	/** Accesses a bucket indirectly via the segment table. */
	Harris::BucketNode* get_bucket(unsigned int);
	/** Creates / sets a bucket indirectly via the segment table, creating a new
	 * segment if necessary. */
	void set_bucket(unsigned int, Harris::BucketNode *);

	/** Similar deal to Harris::List::CAS -- perform an atomic compare and swap,
	 * taking arguments in the same order as Shalev's paper uses the operation.
	 * @todo There should really just be one CAS implementation... */
	bool CAS(Harris::BucketNode **, Harris::BucketNode *, Harris::BucketNode *);

	/** a CAS used for integers, so that we can double the size of the table. */
	bool CAS(jint *, jint old, jint new_val);

	/** atomic increment of the given integer, for incrementing the count of the
	 * number of elements in the table. */
	jint fetch_and_inc(jint *);

	/** Initializes a bucket by searching fro where its pointer should be from
	 * the parent bucket. */
	void initialize_bucket(unsigned int);

	/** lookup using the bare minimum of input */
	static oop lookup(jchar *chars, int length);

public:
	// The string table
	static StringTable* the_table() { return _the_table; }
	static Harris::List* the_list() { return list; }

	/** sets the high order bit and then reverses the word. */
	static juint so_regularkey(juint key);

	/** reverses the bits in the word */
	static juint so_dummykey(juint key);

	static void create_table() {
		unsigned int i;
		assert(_the_table == NULL, "One string table allowed.");
		assert(list == NULL, "Only one list allowed.");
		_the_table = new StringTable();
		list = new Harris::List();
#ifdef DEBUG
		tf_logv("harris list created at %p", list);
#endif
		_the_table->set_bucket(0, list->get_head());
		for(i=1; i < NUM_SEGMENTS; ++i) {
			_the_table->segments[i] = NULL;
		}
	}

	static void create_table(HashtableBucket* t, int length,
	                         int number_of_entries) {
		unsigned int i;
		assert(_the_table == NULL, "One string table allowed.");
		assert(list == NULL, "Only one list allowed.");
		assert(length == initial_table_size * sizeof(HashtableBucket),
		       "bad shared string size.");
		_the_table = new StringTable(t, number_of_entries);
		list = new Harris::List();
		tf_logv("harris list created at %p", list);
		_the_table->set_bucket(0, list->get_head());
		for(i=1; i < NUM_SEGMENTS; ++i) {
			_the_table->segments[i] = NULL;
		}
	}

  static int hash_string(jchar* s, int len);

  // GC support
  //   Delete pointers to otherwise-unreachable objects.
  static void unlink(BoolObjectClosure* cl) {
    the_table()->Hashtable::unlink(cl);
  }

  // Invoke "f->do_oop" on the locations of all oops in the table.
  static void oops_do(OopClosure* f) {
    the_table()->Hashtable::oops_do(f);
  }

  // Probing
  static oop lookup(symbolOop symbol);

  // Interning
  static oop intern(symbolOop symbol, TRAPS);
  static oop intern(oop string, TRAPS);
  static oop intern(const char *utf8_string, TRAPS);

  // Debugging
  static void verify();

  // Sharing
  static void copy_buckets(char** top, char*end) {
    the_table()->Hashtable::copy_buckets(top, end);
  }
  static void copy_table(char** top, char*end) {
    the_table()->Hashtable::copy_table(top, end);
  }
  static void reverse() {
    ((BasicHashtable*)the_table())->reverse();
  }
};
