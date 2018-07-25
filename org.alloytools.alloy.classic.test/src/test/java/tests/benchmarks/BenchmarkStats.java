/*
 * Kodkod -- Copyright (c) 2005-2008, Emina Torlak
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
package tests.benchmarks;

import static tests.util.Reflection.construct;
import static tests.util.Reflection.create;

import java.util.LinkedHashMap;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;

/**
 * Executes a single problem. The output is printed in the following (tab
 * separated) format: <class name> <method name> <universe size> <S|U>
 * <translation time (ms)> <# of gates> <# of primary vars> <# of vars> <# of
 * clauses> <solving time (ms)>
 *
 * @author Emina Torlak
 */
public final class BenchmarkStats {

    private static void usage() {
        System.out.println("Usage: java tests.benchmarks.BenchmarkStats <class name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] [-scope=(<primitive | string | enum>[,<primitive | string | enum>]*)] [-sharing=<sharing depth>] [-symm=<sbp length>]");
        System.exit(1);
    }

    private static class GateReporter extends AbstractReporter {

        int  gates = 0;
        long time;

        // public void solvingCNF(int primaryVars, int vars, int clauses) {
        // System.out.println("About to start solving, p cnf : " + vars + " " +
        // clauses);
        // System.out.println("Primary vars and gates : " + primaryVars + " " +
        // gates);
        // }
        @Override
        public void translatingToCNF(BooleanFormula v) {
            final long start = System.currentTimeMillis();
            final IntSet s = new IntTreeSet();
            final BooleanVisitor<Object,Object> counter = new BooleanVisitor<Object,Object>() {

                @Override
                public Object visit(MultiGate multigate, Object arg) {
                    if (s.add(multigate.label())) {
                        for (BooleanFormula f : multigate) {
                            f.accept(this, arg);
                        }
                    }
                    return null;
                }

                @Override
                public Object visit(ITEGate ite, Object arg) {
                    if (s.add(ite.label())) {
                        for (BooleanFormula f : ite) {
                            f.accept(this, arg);
                        }
                    }
                    return null;
                }

                @Override
                public Object visit(NotGate negation, Object arg) {
                    if (s.add(negation.label())) {
                        negation.input(0).accept(this, arg);
                    }
                    return null;
                }

                @Override
                public Object visit(BooleanVariable variable, Object arg) {
                    return null;
                }

            };
            v.accept(counter, null);
            gates = s.size();

            final long end = System.currentTimeMillis();
            time = end - start;
        }
    }

    /**
     * Returns a map that maps each option in the given argument array to its value,
     * or null if the option has no value. Assumes that all options are of the form
     * "-opt=val" or "-opt".
     *
     * @return a map that maps each option in the given argument array to its value,
     *         or null if the option has no value.
     */
    static Map<String,String> options(String[] args) {
        final Map<String,String> opts = new LinkedHashMap<String,String>();
        for (String arg : args) {
            if (arg.startsWith("-")) {
                String[] opt = arg.split("=");
                switch (opt.length) {
                    case 1 :
                        opts.put(opt[0], null);
                        break;
                    case 2 :
                        opts.put(opt[0], opt[1]);
                        break;
                    default :
                        throw new IllegalArgumentException("Unrecognized option format: " + arg);
                }
            }
        }
        return opts;
    }

    /**
     * Usage: java tests.benchmarks.BenchmarkStats <class name>[(<primitive | string
     * | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string |
     * enum>[,<primitive | string | enum>]*)] [-scope=<method name>(<primitive |
     * string | enum>[,<primitive | string | enum>]*)] [-sharing=<sharing depth>]
     * [-symm=<sbp length>]
     */
    public static void main(String[] args) {
        if (args.length < 2)
            usage();

        try {
            final Map<String,String> opts = options(args);

            final Object instance = construct(args[0].contains("(") ? args[0] : args[0] + "()");
            final Formula formula = create(instance, args[1].contains("(") ? args[1] : args[1] + "()");
            final Bounds bounds = create(instance, opts.containsKey("-scope") ? opts.get("-scope") : "bounds()");

            final GateReporter reporter = new GateReporter();
            final Solver solver = new Solver();
            solver.options().setSolver(SATFactory.MiniSat);
            solver.options().setBitwidth(8);
            solver.options().setLogTranslation(0);
            solver.options().setReporter(reporter);
            if (opts.containsKey("-sharing"))
                solver.options().setSharing(Integer.parseInt(opts.get("-sharing")));
            if (opts.containsKey("-symm"))
                solver.options().setSymmetryBreaking(Integer.parseInt(opts.get("-symm")));

            // <class name> <method name> <universe size>
            System.out.print(args[0].split("\\(")[0] + "\t");
            System.out.print(args[1].split("\\(")[0] + "\t");
            System.out.print(bounds.universe().size() + "\t");
            final Solution sol = solver.solve(formula, bounds);

            // <S|U> <translation time (ms)> <# of gates> <# of primary vars> <#
            // of vars> <# of clauses> <solving time (ms)>
            System.out.print((sol.instance() == null ? "U" : "S") + "\t");
            System.out.print((sol.stats().translationTime() - reporter.time) + "\t");
            System.out.print(reporter.gates + "\t");
            System.out.print(sol.stats().primaryVariables() + "\t");
            System.out.print(sol.stats().variables() + "\t");
            System.out.print(sol.stats().clauses() + "\t");
            System.out.println(sol.stats().solvingTime());

        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
