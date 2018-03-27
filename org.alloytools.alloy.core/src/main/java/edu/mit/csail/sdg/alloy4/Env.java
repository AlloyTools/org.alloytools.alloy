/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;

/**
 * Mutable; implements a undoable map based on hashCode() and equals(); null key
 * and values are allowed.
 * <p>
 * To be more precise, every key is internally mapped to a list of values. <br>
 * The put(X,Y) method appends Y onto the end of X's list. <br>
 * The get(X) method returns the last element in X's list. <br>
 * The remove(X) method removes the last element in X's list.
 * <p>
 * This is very useful for representing lexical scoping: when a local variable
 * is introduced with the same name as an existing variable, the new variable
 * "hides" the old mapping; and when the new variable falls out of scope, the
 * previous mapping is once again "revealed".
 *
 * @param <V> - the type for Value
 */

public final class Env<K, V> {

    /**
     * If a key is bound to one or more values, this stores the first value.
     * <p>
     * For example: if key K is bound to list of values V1,V2,V3...Vn, then
     * map1.get(K) returns V1
     * <p>
     * Invariant: map2.containsKey(x) implies (map1.containsKey(x) &&
     * map2.get(x).size()>0)
     */
    private final Map<K,V>             map1 = new LinkedHashMap<K,V>();

    /**
     * If a key is bound to more than one value, this stores every value except the
     * first value.
     * <p>
     * For example: if key K is bound to list of values V1,V2,V3...Vn, then
     * map2.get(K) returns the sublist V2..Vn
     * <p>
     * Invariant: map2.containsKey(x) implies (map1.containsKey(x) &&
     * map2.get(x).size()>0)
     */
    private final Map<K,LinkedList<V>> map2 = new LinkedHashMap<K,LinkedList<V>>();

    /** Constructs an initially empty environment. */
    public Env() {}

    /**
     * Returns true if the key is mapped to one or more values.
     */
    public boolean has(K key) {
        return map1.containsKey(key);
    }

    /**
     * Returns the latest value associated with the key (and returns null if none).
     * <p>
     * Since null is also a possible value, if you get null as the answer, you need
     * to call has(key) to determine whether the key really has a mapping or not.
     */
    public V get(K key) {
        LinkedList<V> list = map2.get(key);
        return (list != null) ? list.getLast() : map1.get(key);
    }

    /**
     * Associates the key with the value (which can be null).
     */
    public void put(K key, V value) {
        LinkedList<V> list = map2.get(key);
        if (list != null) {
            list.add(value);
        } else if (!map1.containsKey(key)) {
            map1.put(key, value);
        } else {
            list = new LinkedList<V>();
            list.add(value);
            map2.put(key, list);
        }
    }

    /**
     * Removes the latest mapping for the key (and if the key had previous mappings,
     * they become visible). If there are no mappings for the key, then this method
     * does nothing.
     */
    public void remove(K key) {
        LinkedList<V> list = map2.get(key);
        if (list == null)
            map1.remove(key);
        else if (list.size() == 1)
            map2.remove(key);
        else
            list.removeLast();
    }

    /** Removes all mappings. */
    public void clear() {
        map1.clear();
        map2.clear();
    }

    /** Make a shallow copy of this environment. */
    public Env<K,V> dup() {
        Env<K,V> ans = new Env<K,V>();
        ans.map1.putAll(map1);
        for (Map.Entry<K,LinkedList<V>> e : map2.entrySet())
            ans.map2.put(e.getKey(), new LinkedList<V>(e.getValue()));
        return ans;
    }
}
