package org.sat4j;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import org.junit.Test;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.GateTranslator;
import org.sat4j.tools.ModelIterator;

public class BugSAT117ModelIterator {
    private final GateTranslator gateTranslator;
    private final ISolver solver;
    private final ModelIterator modelIterator;

    @Test
    public void testIt() {
        Date begin = new Date();
        long beginTime = begin.getTime();

        Date now = new Date();
        while (now.getTime() - beginTime < 60000) {
            solve();
            now = new Date();
        }
    }

    private List<List<Integer>> solve() {
        List<List<Integer>> solution = new ArrayList<List<Integer>>();
        solver.newVar(5);

        // (x1 ? �x5 ? x4) ? (�x1 ? x5 ? x3 ? x4)
        try {
            gateTranslator.not(6, 5);
            IVecInt disjuncts1 = new VecInt(new int[] { 1, 6, 4 });
            gateTranslator.or(7, disjuncts1);
            gateTranslator.not(8, 1);
            IVecInt disjuncts2 = new VecInt(new int[] { 8, 5, 3, 4 });
            gateTranslator.or(9, disjuncts2);
            gateTranslator.gateTrue(9);
            while (modelIterator.isSatisfiable()) {
                final int[] model = modelIterator.model();
                List<Integer> modelList = new ArrayList<Integer>(model.length);
                for (int literal : model) {
                    modelList.add(literal);
                }
                solution.add(modelList);
            }
        } catch (ContradictionException ex) {
            ex.printStackTrace();
        } catch (TimeoutException ex) {
            ex.printStackTrace();
        } finally {
            gateTranslator.reset();
            solver.reset();
            modelIterator.reset();
        }

        return solution;
    }

    public BugSAT117ModelIterator() {
        solver = SolverFactory.newLight();
        gateTranslator = new GateTranslator(solver);
        modelIterator = new ModelIterator(solver);
    }
}
