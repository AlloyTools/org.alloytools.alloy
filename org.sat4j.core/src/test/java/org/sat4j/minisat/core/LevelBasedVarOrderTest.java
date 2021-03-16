package org.sat4j.minisat.core;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.orders.LevelBasedVarOrderHeap;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.SearchListenerAdapter;
import org.sat4j.specs.TimeoutException;

public class LevelBasedVarOrderTest {

    @Test
    public void test() throws ContradictionException, TimeoutException {
        ICDCL<? extends DataStructureFactory> solver = (ICDCL<? extends DataStructureFactory>) SolverFactory
                .newDefault();
        LevelBasedVarOrderHeap order = new LevelBasedVarOrderHeap();
        solver.setOrder(order);
        solver.newVar(5);
        IVecInt clause = new VecInt();
        clause.push(1).push(2).push(3).push(4).push(5);
        solver.addClause(clause);
        order.addLevel(new int[] { 4, 5 });
        order.addLevel(new int[] { 2, 3 });
        final IVec<IVecInt> expected = new Vec<IVecInt>();
        expected.push(new VecInt(new int[] { 2, 3 })).push(
                new VecInt(new int[] { 4, 5 }));
        solver.setSearchListener(new SearchListenerAdapter<ISolverService>() {
            private static final long serialVersionUID = 1L;

            @Override
            public void assuming(int p) {
                int v = p > 0 ? p : -p;
                if (!expected.isEmpty()) {
                    IVecInt vars = expected.last();
                    assert !vars.isEmpty();
                    assertTrue(vars.contains(v));
                    vars.remove(v);
                    if (vars.isEmpty()) {
                        expected.pop();
                    }
                }
            }
        });
        assertTrue(solver.isSatisfiable());
    }
}
