/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.satlab;

import java.util.NoSuchElementException;

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * A wrapper class that provides access to the basic funcionality of the MiniSAT
 * solvers (org.sat4j.specs.ISolver) from CRIL.
 *
 * @author Emina Torlak
 */
final class SAT4J implements SATSolver {

    private ISolver               solver;
    private final ReadOnlyIVecInt wrapper;
    private Boolean               sat;
    private int                   vars, clauses;

    /**
     * Constructs a wrapper for the given instance of ISolver.
     *
     * @throws NullPointerException solver = null
     */
    SAT4J(ISolver solver) {
        if (solver == null)
            throw new NullPointerException("solver");
        this.solver = solver;
        this.wrapper = new ReadOnlyIVecInt();
        this.sat = null;
        this.vars = this.clauses = 0;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
     */
    @Override
    public int numberOfVariables() {
        return vars;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
     */
    @Override
    public int numberOfClauses() {
        return clauses;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#addVariables(int)
     */
    @Override
    public void addVariables(int numVars) {
        if (numVars < 0)
            throw new IllegalArgumentException("numVars < 0: " + numVars);
        else if (numVars > 0) {
            vars += numVars;
            solver.newVar(vars);
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#addClause(int[])
     */
    @Override
    public boolean addClause(int[] lits) {
        try {
            if (!Boolean.FALSE.equals(sat)) {
                clauses++;
                solver.addClause(wrapper.wrap(lits));
                // for(int lit : lits) {
                // System.out.print(lit + " ");
                // }
                // System.out.println(0);
                return true;
            }

        } catch (ContradictionException e) {
            sat = Boolean.FALSE;
        }
        return false;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#solve()
     */
    @Override
    public boolean solve() {
        try {
            if (solver == null)
                return false;
            if (!Boolean.FALSE.equals(sat))
                sat = Boolean.valueOf(solver.isSatisfiable());
            return sat;
        } catch (org.sat4j.specs.TimeoutException e) {
            throw new RuntimeException("timed out");
        }
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#valueOf(int)
     */
    @Override
    public final boolean valueOf(int variable) {
        if (!Boolean.TRUE.equals(sat))
            throw new IllegalStateException();
        if (variable < 1 || variable > vars)
            throw new IllegalArgumentException(variable + " !in [1.." + vars + "]");
        return solver.model(variable);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.satlab.SATSolver#free()
     */
    @Override
    public synchronized final void free() {
        sat = Boolean.FALSE;
        solver = null;
    }

    /**
     * A wrapper for an int array that provides read-only access to the array via
     * the IVecInt interface.
     *
     * @author Emina Torlak
     */
    private static final class ReadOnlyIVecInt implements IVecInt {

        private static final long serialVersionUID = -7689441271777278043L;
        private int[]             vec;

        /**
         * Sets this.vec to the given vector and returns this.
         */
        IVecInt wrap(int[] vec) {
            this.vec = vec;
            return this;
        }

        @Override
        public int size() {
            return vec.length;
        }

        @Override
        public boolean isEmpty() {
            return size() == 0;
        }

        @Override
        public int unsafeGet(int arg0) {
            return vec[arg0];
        }

        @Override
        public int last() {
            return vec[vec.length - 1];
        }

        @Override
        public int[] toArray() {
            return vec;
        }

        @Override
        public int get(int arg0) {
            if (arg0 < 0 || arg0 >= vec.length)
                throw new IndexOutOfBoundsException("arg0: " + arg0);
            return vec[arg0];
        }

        @Override
        public boolean contains(int arg0) {
            final int[] workArray = vec; // faster access
            for (int i : workArray) {
                if (i == arg0)
                    return true;
            }
            return false;
        }

        @Override
        public void copyTo(IVecInt arg0) {
            int argLength = arg0.size();
            final int[] workArray = vec; // faster access
            arg0.ensure(argLength + workArray.length);
            for (int i : workArray) {
                arg0.set(argLength++, i);
            }
        }

        @Override
        public void copyTo(int[] arg0) {
            assert arg0.length >= vec.length;
            System.arraycopy(vec, 0, arg0, 0, vec.length);
        }

        @Override
        public IteratorInt iterator() {
            return new IteratorInt() {

                int cursor = 0;

                @Override
                public boolean hasNext() {
                    return cursor < vec.length;
                }

                @Override
                public int next() {
                    if (!hasNext())
                        throw new NoSuchElementException();
                    return vec[cursor++];
                }
            };
        }

        @Override
        public int containsAt(int e) {
            final int[] workArray = vec; // faster access
            for (int n = workArray.length, i = 0; i < n; i++)
                if (workArray[i] == e)
                    return i;
            return -1;
        }

        @Override
        public int containsAt(int e, int from) {
            final int[] workArray = vec; // faster access
            if (from < workArray.length)
                for (int n = workArray.length, i = from + 1; i < n; i++)
                    if (workArray[i] == e)
                        return i;
            return -1;
        }

        @Override
        public int indexOf(int e) {
            final int[] workArray = vec; // faster access
            for (int i = 0, n = workArray.length; i < n; i++) {
                if (workArray[i] == e)
                    return i;
            }
            return -1;
        }

        // unsupported
        @Override
        public void shrink(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void shrinkTo(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public IVecInt pop() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void growTo(int arg0, int arg1) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void ensure(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public IVecInt push(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void unsafePush(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void clear() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void moveTo(IVecInt arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void moveTo2(IVecInt arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void moveTo(int[] arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void moveTo(int arg0, int arg1) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void moveTo(int i, int[] arg1) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void insertFirst(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void remove(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int delete(int arg0) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void set(int arg0, int arg1) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void sort() {
            throw new UnsupportedOperationException();
        }

        @Override
        public void sortUnique() {
            throw new UnsupportedOperationException();
        }

        @Override
        public IVecInt[] subset(int arg0) {
            throw new UnsupportedOperationException();
        }
    }

    public static void main(String[] args) {
        final SAT4J z = (SAT4J) SATFactory.DefaultSAT4J.instance();
        // z.addVariables(3);
        // int[] clause = {1,2,3};
        // z.addClause(clause);
        // int[] clause1 = {-3};
        // z.addClause(clause1);
        // System.out.println(z.solver.nVars());
        // z.addVariables(4);
        // System.out.println(z.solver.nVars());
        // clause1[0] = 7;
        // z.addClause(clause1);
        z.addVariables(1);
        int[] clause1 = {
                         1
        };
        z.addClause(clause1);
        clause1[0] = -1;
        z.addClause(clause1);

        System.out.println(z.solve());
        // System.out.println(z.variablesThatAre(true, 1, 1));

    }

}
