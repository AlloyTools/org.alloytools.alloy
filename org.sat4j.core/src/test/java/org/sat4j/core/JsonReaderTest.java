package org.sat4j.core;

import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.inOrder;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

import org.junit.Before;
import org.junit.Test;
import org.mockito.InOrder;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.JSONReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

public class JsonReaderTest {

    private ISolver solver;
    private JSONReader<ISolver> reader;

    @Before
    public void setUp() throws Exception {
        solver = mock(ISolver.class);
        reader = new JSONReader<ISolver>(solver);
    }

    @Test
    public void testReadingSimpleClause() throws ParseFormatException,
            ContradictionException, IOException {
        String json = "[[1,-2,3]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addClause(clause);

    }

    @Test(expected = ContradictionException.class)
    public void testReadingNullClause() throws ParseFormatException,
            ContradictionException, IOException {
        when(solver.addClause(VecInt.EMPTY)).thenThrow(
                new ContradictionException());
        String json = "[[]]";
        reader.parseString(json);
        IVecInt clause = new VecInt();
        verify(solver).addClause(clause);
    }

    @Test
    public void testReadingTwoClauses() throws ParseFormatException,
            ContradictionException, IOException {
        when(solver.addClause(VecInt.EMPTY)).thenThrow(
                new ContradictionException());
        String json = "[[1,2,5],[3,-6]]";
        reader.parseString(json);
        IVecInt clause1 = new VecInt().push(1).push(2).push(5);
        IVecInt clause2 = new VecInt().push(3).push(-6);
        InOrder inOrder = inOrder(solver);
        inOrder.verify(solver).addClause(clause1);
        inOrder.verify(solver).addClause(clause2);

    }

    @Test
    public void testReadingACardExactly() throws ParseFormatException,
            ContradictionException {
        String json = "[[[1,-2,3],'=',1]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addExactly(clause, 1);
    }

    @Test
    public void testReadingACardAtMostEqual() throws ParseFormatException,
            ContradictionException {
        String json = "[[[1,-2,3],'<=',1]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addAtMost(clause, 1);
    }

    @Test
    public void testReadingACardAtMostStrictly() throws ParseFormatException,
            ContradictionException {
        String json = "[[[1,-2,3],'<',1]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addAtMost(clause, 0);
    }

    @Test
    public void testReadingACardAtLeastEqual() throws ParseFormatException,
            ContradictionException {
        String json = "[[[1,-2,3],'>=',2]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addAtLeast(clause, 2);
    }

    @Test
    public void testReadingACardAtLeastStrictly() throws ParseFormatException,
            ContradictionException {
        String json = "[[[1,-2,3],'>',2]]";
        reader.parseString(json);
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addAtLeast(clause, 3);
    }

    @Test
    public void testMixOfClausesAndCard() throws ParseFormatException,
            ContradictionException {
        String json = "[[-1,-2,-3],[[1,-2,3],'>',2],[4,-3,6]]";
        reader.parseString(json);
        IVecInt clause1 = new VecInt().push(-1).push(-2).push(-3);
        IVecInt card = new VecInt().push(1).push(-2).push(3);
        IVecInt clause2 = new VecInt().push(4).push(-3).push(6);
        verify(solver).addClause(clause1);
        verify(solver).addAtLeast(card, 3);
        verify(solver).addClause(clause2);
    }

    @Test
    public void testOrderofMixedConstraints() throws ParseFormatException,
            ContradictionException {
        String json = "[[-1,-2,-3],[[1,-2,3],'>',2],[4,-3,6]]";
        reader.parseString(json);
        IVecInt clause1 = new VecInt().push(-1).push(-2).push(-3);
        IVecInt card = new VecInt().push(1).push(-2).push(3);
        IVecInt clause2 = new VecInt().push(4).push(-3).push(6);
        InOrder inOrder = inOrder(solver);
        inOrder.verify(solver).addClause(clause1);
        inOrder.verify(solver).addAtLeast(card, 3);
        inOrder.verify(solver).addClause(clause2);
    }

    @Test
    public void testInputStream() throws ParseFormatException,
            ContradictionException, IOException {
        String json = "[[[1,-2,3],'>',2]]";
        reader.parseInstance(new ByteArrayInputStream(json.getBytes()));
        IVecInt clause = new VecInt().push(1).push(-2).push(3);
        verify(solver).addAtLeast(clause, 3);
    }

    @Test
    public void testJsonOutput() throws ParseFormatException,
            ContradictionException, TimeoutException {
        String json = "[[1,-2,3],[1,2,3],[1,-3],[-1,-3],[-1,2,3]]";
        ISolver realSolver = SolverFactory.newDefault();
        JSONReader jsonReader = new JSONReader(realSolver);
        jsonReader.parseString(json);
        int[] model = realSolver.findModel();
        StringWriter strw = new StringWriter();
        PrintWriter out = new PrintWriter(strw);
        jsonReader.decode(model, out);
        assertEquals("[1,2,-3]", strw.toString());
    }
}
