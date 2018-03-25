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

import java.util.HashSet;
import java.util.Set;

/**
 * This generates unique names based on names provided by the caller.
 * <p>
 * <b>Thread Safety:</b> Safe.
 */

public final class UniqueNameGenerator {

    /** This stores the set of names we've generated so far. */
    private final Set<String> names = new HashSet<String>();

    /** Construct a UniqueNameGenerator with a blank history. */
    public UniqueNameGenerator() {}

    /**
     * Regard the provided name as "seen".
     * <p>
     * For convenience, it returns the argument as the return value.
     */
    public synchronized String seen(String name) {
        names.add(name);
        return name;
    }

    /**
     * Queries whether the provided name has been "seen" or not.
     */
    public synchronized boolean hasSeen(String name) {
        return names.contains(name);
    }

    /** Clear the history of previously generated names. */
    public synchronized void clear() {
        names.clear();
    }

    /**
     * Generate a unique name based on the input name.
     * <p>
     * Specifically: if the name has not been generated/seen already by this
     * generator, then it is returned as is. Otherwise, we append ' to it until the
     * name becomes unique.
     */
    public synchronized String make(String name) {
        while (!names.add(name))
            name = name + "'";
        return name;
    }
}
