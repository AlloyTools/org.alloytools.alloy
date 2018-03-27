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
package kodkod.engine.config;

import java.util.List;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.hol.HOLTranslation;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.util.ints.IntSet;

/**
 * An implementation of the reporter interface that prints messages to the
 * standard output stream.
 *
 * @author Emina Torlak
 */
public final class ConsoleReporter implements Reporter {

    /**
     * Constructs a new instance of the ConsoleReporter.
     */
    public ConsoleReporter() {}

    /**
     * @see kodkod.engine.config.Reporter#generatingSBP()
     */
    @Override
    public void generatingSBP() {
        System.out.println("generating lex-leader symmetry breaking predicate ...");
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.config.Reporter#skolemizing(kodkod.ast.Decl,
     *      kodkod.ast.Relation, java.util.List)
     */
    @Override
    public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {
        System.out.println("skolemizing " + decl + ": skolem relation=" + skolem + ", arity=" + skolem.arity());
    }

    /**
     * @see kodkod.engine.config.Reporter#solvingCNF(int, int, int)
     */
    @Override
    public void solvingCNF(int primaryVars, int vars, int clauses) {
        System.out.println("solving p cnf " + vars + " " + clauses);
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.config.Reporter#detectingSymmetries(kodkod.instance.Bounds)
     */
    @Override
    public void detectingSymmetries(Bounds bounds) {
        System.out.println("detecting symmetries ...");
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.engine.config.Reporter#detectedSymmetries(java.util.Set)
     */
    @Override
    public void detectedSymmetries(Set<IntSet> parts) {
        System.out.println("detected " + parts.size() + " equivalence classes of atoms ...");
    }

    /**
     * @see kodkod.engine.config.Reporter#optimizingBoundsAndFormula()
     */
    @Override
    public void optimizingBoundsAndFormula() {
        System.out.println("optimizing bounds and formula (breaking predicate symmetries, inlining, skolemizing) ...");
    }

    /**
     * @see kodkod.engine.config.Reporter#translatingToBoolean(kodkod.ast.Formula,
     *      kodkod.instance.Bounds)
     */
    @Override
    public void translatingToBoolean(Formula formula, Bounds bounds) {
        System.out.println("translating to boolean ...");
    }

    /**
     * @see kodkod.engine.config.Reporter#translatingToCNF(kodkod.engine.bool.BooleanFormula)
     */
    @Override
    public void translatingToCNF(BooleanFormula circuit) {
        System.out.println("translating to cnf ...");
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "ConsoleReporter";
    }

    @Override
    public void convertingToNNF() {
        System.out.println("converting to nnf ...");

    }

    @Override
    public void holLoopStart(HOLTranslation tr, Formula formula, Bounds bounds) {
        System.out.println(String.format("starting higher-order (%s) search ...", tr));
    }

    @Override
    public void holCandidateFound(HOLTranslation tr, Instance candidate) {
        System.out.println(String.format("  [%s] candidate found", tr));
    }

    @Override
    public void holVerifyingCandidate(HOLTranslation tr, Instance candidate, Formula checkFormula, Bounds bounds) {
        System.out.println(String.format("  [%s]   verifying candidate", tr));
    }

    @Override
    public void holCandidateVerified(HOLTranslation tr, Instance candidate) {
        System.out.println(String.format("  [%s]   candidate verified", tr));
    }

    @Override
    public void holCandidateNotVerified(HOLTranslation tr, Instance candidate, Instance cex) {
        System.out.println(String.format("  [%s]   counterexample found", tr));
    }

    @Override
    public void holFindingNextCandidate(HOLTranslation tr, Formula inc) {
        System.out.println(String.format("  [%s] continuing cegis loop", tr.getClass()));
    }

    @Override
    public void holSplitStart(HOLTranslation tr, Formula formula) {
        System.out.println(String.format("starting split (%s) ...", tr));
    }

    @Override
    public void holSplitChoice(HOLTranslation tr, Formula formula, Bounds bounds) {
        System.out.println(String.format("  [%s] trying choice", tr));
    }

    @Override
    public void holSplitChoiceSAT(HOLTranslation tr, Instance interpret) {
        System.out.println(String.format("  [%s] choice SAT", tr));
    }

    @Override
    public void holSplitChoiceUNSAT(HOLTranslation tr) {
        System.out.println(String.format("  [%s] choice UNSAT", tr));
    }

    @Override
    public void holFixpointStart(HOLTranslation tr, Formula formula, Bounds bounds) {
        System.out.println(String.format("  [%s] fixpoint search started", tr));
    }

    @Override
    public void holFixpointNoSolution(HOLTranslation tr) {
        System.out.println(String.format("  [%s]   no solution", tr));
    }

    @Override
    public void holFixpointFirstSolution(HOLTranslation tr, Instance candidate) {
        System.out.println(String.format("  [%s]   first solution found", tr));
    }

    @Override
    public void holFixpointIncrementing(HOLTranslation tr, Formula inc) {
        System.out.println(String.format("  [%s]   hill climbing", tr));
    }

    @Override
    public void holFixpointIncrementingOutcome(HOLTranslation tr, Instance next) {
        if (next != null)
            System.out.println(String.format("  [%s]   climbed one step", tr));
        else
            System.out.println(String.format("  [%s]   fixpoint reached", tr));
    }

}
