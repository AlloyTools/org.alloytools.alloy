package org.sat4j;

import java.io.IOException;

import org.junit.Test;
import org.mockito.Mockito;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;

public class BugSAT145 {

    @Test
    public void testWindowsPath()
            throws ParseFormatException, IOException, ContradictionException {
        Reader mockReader = Mockito.mock(Reader.class);
        InstanceReader instanceReader = new InstanceReader(
                SolverFactory.newDefault(), mockReader);
        instanceReader
                .parseInstance("EZCNF:C:\\projects\\bla\\testcomments.cnf");
        Mockito.verify(mockReader)
                .parseInstance("C:\\projects\\bla\\testcomments.cnf");

    }

    @Test
    public void testUnixPath()
            throws ParseFormatException, IOException, ContradictionException {
        Reader mockReader = Mockito.mock(Reader.class);
        InstanceReader instanceReader = new InstanceReader(
                SolverFactory.newDefault(), mockReader);
        instanceReader.parseInstance("EZCNF:/projects/bla/testcomments.cnf");
        Mockito.verify(mockReader)
                .parseInstance("/projects/bla/testcomments.cnf");

    }
}
