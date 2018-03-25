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

package edu.mit.csail.sdg.translator;

import java.io.IOException;
import java.io.RandomAccessFile;

import edu.mit.csail.sdg.alloy4.Util;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;

/**
 * An implementation of SATSolver that dumps the CNF to a file and then throws
 * an exception (this code is adapted from ExternalSolver from Kodkod).
 */

final class WriteCNF implements SATSolver {

    /**
     * This runtime exception is thrown when the CNF file has been written
     * successfully.
     */
    public static final class WriteCNFCompleted extends RuntimeException {

        /** This ensures the class can be serialized reliably. */
        private static final long serialVersionUID = 0;

        /** This constructs a new WriteCNFCompleted exception. */
        public WriteCNFCompleted() {
            super("CNF written successfully.");
        }
    }

    /** This is the CNF file we are generating. */
    private final RandomAccessFile cnf;

    /**
     * This buffers up the clauses we are writing to the CNF file, to avoid
     * excessive I/O.
     */
    private final StringBuilder    buffer;

    /** This is the buffer size. */
    private static final int       capacity = 8192;

    /** The number of variables so far. */
    private int                    vars     = 0;

    /** The number of clauses so far. */
    private int                    clauses  = 0;

    /**
     * Helper method that returns a factory for WriteCNF instances.
     */
    public static final SATFactory factory(final String filename) {
        return new SATFactory() {

            /** {@inheritDoc} */
            @Override
            public SATSolver instance() {
                return new WriteCNF(filename);
            }

            /** {@inheritDoc} */
            @Override
            public boolean incremental() {
                return false;
            }
        };
    }

    /**
     * Constructs a WriteCNF solver that will write CNF into the given file, without
     * solving it.
     */
    private WriteCNF(String filename) {
        try {
            this.cnf = new RandomAccessFile(filename, "rw");
            this.cnf.setLength(0);
            this.buffer = new StringBuilder(capacity);
            for (int i = String.valueOf(Integer.MAX_VALUE).length() * 2 + 8; i > 0; i--) {
                // get enough space into the buffer for the cnf header, which
                // will be written last
                buffer.append(' ');
            }
            buffer.append('\n');
        } catch (Exception ex) {
            throw new RuntimeException("WriteCNF failed.", ex);
        }
    }

    /** Helper method that flushes the buffer. */
    private void flush() {
        try {
            cnf.writeBytes(buffer.toString());
            buffer.setLength(0);
        } catch (IOException ex) {
            throw new RuntimeException("WriteCNF failed.", ex);
        }
    }

    /** {@inheritDoc} */
    @Override
    protected void finalize() throws Throwable {
        super.finalize();
        free();
    }

    /** {@inheritDoc} */
    @Override
    public void free() {
        Util.close(cnf);
    }

    /** {@inheritDoc} */
    @Override
    public void addVariables(int numVars) {
        if (numVars >= 0)
            vars += numVars;
    }

    /** {@inheritDoc} */
    @Override
    public boolean addClause(int[] lits) {
        if (lits.length > 0) {
            clauses++;
            if (buffer.length() > capacity)
                flush();
            for (int i = 0; i < lits.length; i++)
                buffer.append(lits[i]).append(' ');
            buffer.append("0\n");
            return true;
        }
        return false;
    }

    /** {@inheritDoc} */
    @Override
    public int numberOfVariables() {
        return vars;
    }

    /** {@inheritDoc} */
    @Override
    public int numberOfClauses() {
        return clauses;
    }

    /** {@inheritDoc} */
    @Override
    public boolean solve() {
        try {
            flush();
            cnf.seek(0);
            cnf.writeBytes("p cnf " + vars + " " + clauses);
            cnf.close();
        } catch (Exception ex) {
            throw new RuntimeException("WriteCNF failed.", ex);
        }
        throw new WriteCNFCompleted();
    }

    /** {@inheritDoc} */
    @Override
    public boolean valueOf(int variable) {
        throw new IllegalStateException("This solver just writes the CNF without solving them.");
    }
}
