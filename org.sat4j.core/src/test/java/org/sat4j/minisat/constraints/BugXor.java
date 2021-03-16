package org.sat4j.minisat.constraints;

import static org.junit.Assert.assertEquals;

import java.io.IOException;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class BugXor {

    private ISolver solver;

    @Before
    public void setUp()
            throws IOException, ContradictionException, ParseFormatException {
        solver = SolverFactory.newDefault();
        Reader reader = new DimacsReader(solver);
        reader.parseInstance("src/test/testfiles/jnh/jnh218.cnf");
    }

    @Test
    public void test() throws TimeoutException, ContradictionException {
        IVecInt lits = VecInt.of(1, 2, 3, 4, 6, 8, 10, 17, 20, 25, 26, 38, 39,
                42, 45, 46, 47, 49, 54, 55, 56, 57, 58, 64, 70, 71, 73, 76, 77,
                78, 79, 80, 82, 85, 86, 87, 96, 99);
        solver.addParity(lits, false);
        long count = 0;
        try {
            while (solver.isSatisfiable()) {
                solver.discardCurrentModel();
                count++;
            }
        } catch (ContradictionException e) {
            // normal when the formula becomes unsat
        }
        assertEquals(7027, count);
    }
}
