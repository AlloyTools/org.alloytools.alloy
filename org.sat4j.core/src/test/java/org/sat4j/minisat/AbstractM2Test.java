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
package org.sat4j.minisat;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ISolver;

/**
 * Class responsability.
 * 
 * @author leberre
 * 
 */
public abstract class AbstractM2Test<T extends ISolver> extends
        AbstractAcceptanceTestCase<T> {

    // private static final String PREFIX = "C:\\Documents and
    // Settings\\Daniel\\Mes documents\\SAT\\";
    protected static final String PREFIX = System.getProperty("test.prefix");

    public AbstractM2Test() {
    }

    /**
     * Constructor for DPLLTest.
     * 
     * @param arg0
     */
    public AbstractM2Test(String arg0) {
        super(arg0);
    }

    public void testAim50SAT1() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-1_6-yes1-1.cnf"));
    }

    public void testAim50SAT2() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-1_6-yes1-2.cnf"));
    }

    public void testAim50SAT3() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-1_6-yes1-3.cnf"));
    }

    public void testAim50SAT4() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-1_6-yes1-4.cnf"));
    }

    public void testAim50SAT5() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-2_0-yes1-1.cnf"));
    }

    public void testAim50SAT6() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-2_0-yes1-2.cnf"));
    }

    public void testAim50SAT7() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-2_0-yes1-3.cnf"));
    }

    public void testAim50SAT8() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-2_0-yes1-4.cnf"));
    }

    public void testAim50SAT9() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-3_4-yes1-1.cnf"));
    }

    public void testAim50SAT10() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-3_4-yes1-2.cnf"));
    }

    public void testAim50SAT11() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-3_4-yes1-3.cnf"));
    }

    public void testAim50SAT12() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-3_4-yes1-4.cnf"));
    }

    public void testAim50SAT13() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-6_0-yes1-1.cnf"));
    }

    public void testAim50SAT14() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-6_0-yes1-2.cnf"));
    }

    public void testAim50SAT15() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-6_0-yes1-3.cnf"));
    }

    public void testAim50SAT16() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "aim/aim-50-6_0-yes1-4.cnf"));
    }

    public void testAim50UNSAT1() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-1_6-no-1.cnf"));
    }

    public void testAim50UNSAT2() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-1_6-no-2.cnf"));
    }

    public void testAim50UNSAT3() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-1_6-no-3.cnf"));
    }

    public void testAim50UNSAT4() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-1_6-no-4.cnf"));
    }

    public void testAim50UNSAT5() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-2_0-no-1.cnf"));
    }

    public void testAim50UNSAT6() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-2_0-no-2.cnf"));
    }

    public void testAim50UNSAT7() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-2_0-no-3.cnf"));
    }

    public void testAim50UNSAT8() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "aim/aim-50-2_0-no-4.cnf"));
    }

    public void testIi1() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8a1.cnf"));
    }

    public void testIi2() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8a2.cnf"));
    }

    public void testIi3() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8a3.cnf"));
    }

    public void testIi4() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8a4.cnf"));
    }

    public void testIi5() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8b1.cnf"));
    }

    public void testIi6() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8b2.cnf"));
    }

    public void testIi7() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8b3.cnf"));
    }

    public void testIi8() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8b4.cnf"));
    }

    public void testIi9() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8c1.cnf"));
    }

    public void testIi10() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8c2.cnf"));
    }

    public void testIi11() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8d1.cnf"));
    }

    public void testIi12() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8d2.cnf"));
    }

    public void testIi13() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8e1.cnf"));
    }

    public void testIi14() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii8e2.cnf"));
    }

    public void testIi15() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16a1.cnf"));
    }

    public void testIi16() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16a2.cnf"));
    }

    public void testIi17() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16b1.cnf"));
    }

    public void testIi18() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16b2.cnf"));
    }

    // public void testIi19()
    // throws FileNotFoundException, IOException, ParseFormatException {
    // assertTrue(solveInstance(PREFIX + "ii/ii16c1.cnf"));
    // }

    public void testIi20() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16c2.cnf"));
    }

    public void testIi21() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16d1.cnf"));
    }

    public void testIi22() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16d2.cnf"));
    }

    public void testIi23() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "ii/ii16e1.cnf"));
    }

    public void testJNH1() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh1.cnf"));
    }

    public void testJNH2() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh2.cnf"));
    }

    public void testJNH3() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh3.cnf"));
    }

    public void testJNH4() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh4.cnf"));
    }

    public void testJNH5() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh5.cnf"));
    }

    public void testJNH6() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh6.cnf"));
    }

    public void testJNH7() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh7.cnf"));
    }

    public void testJNH8() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh8.cnf"));
    }

    public void testJNH9() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh9.cnf"));
    }

    public void testJNH10() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh10.cnf"));
    }

    public void testJNH11() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh11.cnf"));
    }

    public void testJNH12() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh12.cnf"));
    }

    public void testJNH13() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh13.cnf"));
    }

    public void testJNH14() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh14.cnf"));
    }

    public void testJNH15() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh15.cnf"));
    }

    public void testJNH16() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh16.cnf"));
    }

    public void testJNH17() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh17.cnf"));
    }

    public void testJNH18() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh18.cnf"));
    }

    public void testJNH19() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh19.cnf"));
    }

    public void testJNH20() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh20.cnf"));
    }

    public void testJNH21() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh201.cnf"));
    }

    public void testJNH22() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh202.cnf"));
    }

    public void testJNH23() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh203.cnf"));
    }

    public void testJNH24() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh204.cnf"));
    }

    public void testJNH25() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh205.cnf"));
    }

    public void testJNH26() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh206.cnf"));
    }

    public void testJNH27() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh207.cnf"));
    }

    public void testJNH28() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh208.cnf"));
    }

    public void testJNH29() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh209.cnf"));
    }

    public void testJNH30() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh210.cnf"));
    }

    public void testJNH31() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh211.cnf"));
    }

    public void testJNH32() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh212.cnf"));
    }

    public void testJNH33() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh213.cnf"));
    }

    public void testJNH34() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh214.cnf"));
    }

    public void testJNH35() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh215.cnf"));
    }

    public void testJNH36() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh216.cnf"));
    }

    public void testJNH37() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh217.cnf"));
    }

    public void testJNH38() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh218.cnf"));
    }

    public void testJNH39() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh219.cnf"));
    }

    public void testJNH40() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh220.cnf"));
    }

    public void testJNH41() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(solveInstance(PREFIX + "jnh/jnh301.cnf"));
    }

    public void testJNH42() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh302.cnf"));
    }

    public void testJNH43() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh303.cnf"));
    }

    public void testJNH44() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh304.cnf"));
    }

    public void testJNH45() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh305.cnf"));
    }

    public void testJNH46() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh306.cnf"));
    }

    public void testJNH47() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh307.cnf"));
    }

    public void testJNH48() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh308.cnf"));
    }

    public void testJNH49() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh309.cnf"));
    }

    public void testJNH50() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertTrue(!solveInstance(PREFIX + "jnh/jnh310.cnf"));
    }

    public void testHole6() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertFalse(solveInstance(PREFIX + "pigeons/hole6.cnf"));
    }

    public void testHole7() throws FileNotFoundException, IOException,
            ParseFormatException {
        assertFalse(solveInstance(PREFIX + "pigeons/hole7.cnf"));
    }
}
