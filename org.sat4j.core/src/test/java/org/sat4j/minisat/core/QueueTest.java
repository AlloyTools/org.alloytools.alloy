/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.minisat.core;

import junit.framework.TestCase;

/*
 * Created on 23 oct. 2003
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */

/**
 * @author leberre
 * 
 *         To change the template for this generated type comment go to
 *         Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class QueueTest extends TestCase {

    /**
     * Constructor for QueueTest.
     * 
     * @param arg0
     */
    public QueueTest(String arg0) {
        super(arg0);
    }

    /*
     * @see TestCase#setUp()
     */
    @Override
    protected void setUp() throws Exception {
        this.qu = new IntQueue();
    }

    public void testInsert() {
        this.qu.ensure(15);
        for (int i = 0; i < 15; i++) {
            this.qu.insert(i);
        }
        for (int i = 0; i < 15; i++) {
            assertEquals(i, this.qu.dequeue());
        }
    }

    public void testDequeue() {
        this.qu.insert(1);
        this.qu.insert(2);
        assertEquals(2, this.qu.size());
        int i = this.qu.dequeue();
        assertEquals(1, i);
        this.qu.insert(3);
        assertEquals(2, this.qu.size());
        i = this.qu.dequeue();
        assertEquals(2, i);
        i = this.qu.dequeue();
        assertEquals(3, i);
    }

    public void testClear() {
        assertEquals(0, this.qu.size());
        this.qu.insert(1);
        this.qu.insert(2);
        assertEquals(2, this.qu.size());
        this.qu.clear();
        assertEquals(0, this.qu.size());
        this.qu.insert(1);
        this.qu.insert(2);
        assertEquals(2, this.qu.size());
    }

    public void testSize() {
        assertEquals(0, this.qu.size());
        this.qu.insert(1);
        assertEquals(1, this.qu.size());
        this.qu.insert(2);
        assertEquals(2, this.qu.size());
        this.qu.dequeue();
        assertEquals(1, this.qu.size());
        this.qu.dequeue();
        assertEquals(0, this.qu.size());
    }

    private IntQueue qu;

}
