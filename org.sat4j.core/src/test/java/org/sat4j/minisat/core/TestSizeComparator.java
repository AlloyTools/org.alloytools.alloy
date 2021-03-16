package org.sat4j.minisat.core;

import static org.junit.Assert.assertEquals;

import java.util.Comparator;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.constraints.cnf.Lits;
import org.sat4j.minisat.constraints.cnf.OriginalBinaryClause;
import org.sat4j.minisat.constraints.cnf.OriginalWLClause;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;

public class TestSizeComparator {

    private static final Comparator<Constr> comparator = new SizeComparator();

    private IVec<Constr> constrs;
    private Constr c1;
    private Constr c2;
    private Constr c3;
    private Constr c4;

    private ILits voc;

    @Before
    public void setUp() {
        constrs = new Vec<Constr>();
        voc = new Lits();
        IVecInt clause = new VecInt();
        clause.push(2).push(4);
        c1 = new OriginalBinaryClause(clause, voc);
        clause.clear();
        clause.push(2).push(6).push(8).push(10);
        c2 = new OriginalWLClause(clause, voc);
        clause.clear();
        clause.push(3).push(5).push(7).push(11).push(17);
        c3 = new OriginalWLClause(clause, voc);
        clause.clear();
        clause.push(2).push(6).push(8).push(10).push(18).push(24).push(30);
        c4 = new OriginalWLClause(clause, voc);
        clause.clear();
    }

    @Test
    public void testSizeComparator() {
        constrs.push(c4).push(c3).push(c2).push(c1);
        c1.setActivity(5.0);
        IVecInt clause = new VecInt();
        clause = new VecInt();
        clause.push(2).push(4);
        Constr c5 = new OriginalBinaryClause(clause, voc);
        c5.setActivity(10.0);
        clause.clear();
        clause = new VecInt();
        clause.push(2).push(4);
        Constr c6 = new OriginalBinaryClause(clause, voc);
        c5.setActivity(20.0);
        clause.clear();
        clause = new VecInt();
        clause.push(2).push(4);
        Constr c7 = new OriginalBinaryClause(clause, voc);
        c5.setActivity(30.0);
        clause.clear();
        clause = new VecInt();
        clause.push(2).push(4);
        Constr c8 = new OriginalBinaryClause(clause, voc);
        c5.setActivity(40.0);
        clause.clear();
        constrs.push(c5).push(c6).push(c7).push(c8);
        constrs.sort(comparator);
        assertEquals(c1, constrs.get(0));
        assertEquals(c8, constrs.get(1));
        assertEquals(c7, constrs.get(2));
        assertEquals(c6, constrs.get(3));
        assertEquals(c5, constrs.get(4));
        assertEquals(c2, constrs.get(5));
        assertEquals(c3, constrs.get(6));
        assertEquals(c4, constrs.get(7));
    }

    @Test
    public void testSizeComparatorWithTie() {
        constrs.push(c4).push(c3).push(c2).push(c1);
        constrs.sort(comparator);
        assertEquals(c1, constrs.get(0));
        assertEquals(c2, constrs.get(1));
        assertEquals(c3, constrs.get(2));
        assertEquals(c4, constrs.get(3));
    }

}
