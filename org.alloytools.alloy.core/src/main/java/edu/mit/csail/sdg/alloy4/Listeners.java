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

import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4.Listener.Event;

/** This stores a list of listeners. */

public final class Listeners {

    /** The actual list of listeners. */
    private final ArrayList<Listener> listeners = new ArrayList<Listener>();

    /** Construct a empty list of listeners. */
    public Listeners() {}

    /**
     * Add a listener to this group of listeners (if not already in the list)
     */
    public void add(Listener listener) {
        for (Listener x : listeners)
            if (x == listener)
                return;
        listeners.add(listener);
    }

    /**
     * Send the following zero-argument event to every listener.
     */
    public void fire(Object sender, Event event) {
        for (Listener x : listeners)
            x.do_action(sender, event);
    }

    /**
     * Send the following one-argument event to every listener.
     */
    public void fire(Object sender, Event event, Object arg) {
        for (Listener x : listeners)
            x.do_action(sender, event, arg);
    }
}
