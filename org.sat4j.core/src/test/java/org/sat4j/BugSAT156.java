package org.sat4j;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;

import java.io.IOException;

import org.junit.Before;
import org.junit.Test;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;

public class BugSAT156 {

    private InstanceReader instancereader;
    private Reader mockedReader;

    @Before
    public void setUp() {
        mockedReader = mock(Reader.class);
        instancereader = new InstanceReader(SolverFactory.newDefault(),
                mockedReader);

    }

    @Test
    public void testHttpPrefix()
            throws ParseFormatException, IOException, ContradictionException {
        instancereader.parseInstance("http://path/to/file.cnf");
        verify(mockedReader).parseInstance("file.cnf");
    }

    @Test
    public void testWindowsVolume()
            throws ParseFormatException, IOException, ContradictionException {
        instancereader.parseInstance("j:/myNewBenchmark4711.cnf");
        verify(mockedReader).parseInstance("j:/myNewBenchmark4711.cnf");
    }

    @Test
    public void testFixedPrefix()
            throws ParseFormatException, IOException, ContradictionException {
        instancereader.parseInstance("EZCNF:/path/to/file.cnf");
        verify(mockedReader).parseInstance("/path/to/file.cnf");
    }

}
