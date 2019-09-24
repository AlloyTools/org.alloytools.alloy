/*******************************************************************************************[VecThreads.h]
 * Threads safe  version used in Glucose-Syrup, 2015, Gilles Audemard, Laurent Simon
Copyright (c) 2003-2007, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Glucose_VecThreads_h
#define Glucose_VecThreads_h

#include <assert.h>
#include <new>

#include "mtl/IntTypes.h"
#include "mtl/XAlloc.h"
#include<string.h>

namespace Glucose {

//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T>
class vecThreads {
    T*  data;
    int sz;
    int cap;
    bool lock;
    int nbusers;

    // Don't allow copying (error prone):
    vecThreads<T>&  operator = (vecThreads<T>& other) { assert(0); return *this; }
             vecThreads        (vecThreads<T>& other) { assert(0); }
             
    // Helpers for calculating next capacity:
    static inline int  imax   (int x, int y) { int mask = (y-x) >> (sizeof(int)*8-1); return (x&mask) + (y&(~mask)); }
    //static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }
    static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }

public:
    // Constructors:
    vecThreads()                       : data(NULL) , sz(0)   , cap(0), lock(false), nbusers(0)    { }
    explicit vecThreads(int size)      : data(NULL) , sz(0)   , cap(0), lock(false), nbusers(0)    { growTo(size); }
    vecThreads(int size, const T& pad) : data(NULL) , sz(0)   , cap(0),  lock(false), nbusers(0)   { growTo(size, pad); }
   ~vecThreads()                                                          { clear(true); }

    // Pointer to first element:
    operator T*       (void)           { return data; }

    // Size operations:
    int      size     (void) const     { return sz; }
    void     shrink   (int nelems)     { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     shrink_  (int nelems)     { assert(nelems <= sz); sz -= nelems; }
    int      capacity (void) const     { return cap; }
    void     capacity (int min_cap);
    void     capacityProtected (int min_cap);
    void     growTo   (int size);
    void     growTo   (int size, const T& pad);
    void     clear    (bool dealloc = false);

    // Stack interface:
    void     push  (void)              { if (sz == cap) capacity(sz+1); new (&data[sz]) T(); sz++; }
    void     push  (const T& elem)     { if (sz == cap) capacity(sz+1); data[sz++] = elem; }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }
    void     pop   (void)              { assert(sz > 0); sz--, data[sz].~T(); }
    
    void     startMaintenance();
    void     endMaintenance();
    void     startLoop();
    void     endLoop();

    void     remove(const T &elem) {
        int tmp;
        for(tmp = 0;tmp<sz;tmp++) {
            if(data[tmp]==elem) 
                break;
        }
        if(tmp<sz) {
            assert(data[tmp] == elem);
            data[tmp] = data[sz-1];
            sz = sz - 1;
        }
        
    }
    
    // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const T& operator [] (int index) const { return data[index]; }
    T&       operator [] (int index)       { return data[index]; }

    // Duplicatation (preferred instead):
    void copyTo(vecThreads<T>& copy) const { copy.clear(); copy.growTo(sz); 
	startLoop();for (int i = 0; i < sz; i++) copy[i] = data[i]; endLoop();}
    void moveTo(vecThreads<T>& dest) { 
	assert(false); // This cannot be made thread safe from here.
	dest.clear(true);
	startMaintenance(); 
	dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0;
        endMaintenance(); }
    void memCopyTo(vecThreads<T>& copy) const{
        copy.capacity(cap);
        copy.sz = sz;
        memcpy(copy.data,data,sizeof(T)*cap);
    }

};

template<class T>
void vecThreads<T>::startLoop() {
    bool retry = true;
    while (retry) {
	while(!__sync_bool_compare_and_swap(&lock,false, true));
	if (nbusers >= 0) {nbusers++; retry=false;}
	lock = false;
    }
}

template<class T>
void vecThreads<T>::endLoop() {
    while(!__sync_bool_compare_and_swap(&lock,false, true));
    nbusers--; 
    lock = false;
}

template<class T>
inline void vecThreads<T>::startMaintenance() {
    bool retry = true;
    while (retry) {
	while(!__sync_bool_compare_and_swap(&lock,false, true));
	if (nbusers == 0) {nbusers--; retry=false;}
	lock = false;
    }
}

template<class T>
inline void vecThreads<T>::endMaintenance() {
    while(!__sync_bool_compare_and_swap(&lock,false, true));
    nbusers++; 
    lock = false;
}
template<class T>
inline void vecThreads<T>::capacityProtected(int min_cap) {
	startMaintenance();
	capacity(min_cap);
	endMaintenance();
}

template<class T>
void vecThreads<T>::capacity(int min_cap) {
    if (cap >= min_cap) return;

    int add = imax((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);   // NOTE: grow by approximately 3/2
    if (add > INT_MAX - cap || ((data = (T*)::realloc(data, (cap += add) * sizeof(T))) == NULL) && errno == ENOMEM)
        throw OutOfMemoryException();

 }


template<class T>
void vecThreads<T>::growTo(int size, const T& pad) {
    if (sz >= size) return;
    startMaintenance();
    capacity(size);
    for (int i = sz; i < size; i++) data[i] = pad;
    sz = size; 
    endMaintenance();
}


template<class T>
void vecThreads<T>::growTo(int size) {
    if (sz >= size) return;
    startMaintenance();
    capacity(size);
    for (int i = sz; i < size; i++) new (&data[i]) T();
    sz = size; 
    endMaintenance();
}


template<class T>
void vecThreads<T>::clear(bool dealloc) {
    if (data != NULL){
	startMaintenance();
        for (int i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) free(data), data = NULL, cap = 0; 
        endMaintenance();} }

//=================================================================================================
}

#endif
