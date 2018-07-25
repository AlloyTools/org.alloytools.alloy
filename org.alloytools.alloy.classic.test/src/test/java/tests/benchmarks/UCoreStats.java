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

import static tests.util.Reflection.bounds;
import static tests.util.Reflection.checks;
import static tests.util.Reflection.findClass;
import static tests.util.Reflection.formulaCreator;
import static tests.util.Reflection.invokeAll;
import static tests.util.Reflection.strategy;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.util.nodes.Nodes;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Test unsat core extraction for a single problem.
 *
 * @author Emina Torlak
 */
public final class UCoreStats {

    /**
     * Checks that the given proof of unsatisfiablity for the given problem is
     * miminal. This method assumes that the given proof is correct.
     *
     * @return true if the core is minimal; false otherwise.
     */
    static boolean checkMinimal(Set<Formula> core, Bounds bounds) {
        System.out.print("checking minimality ... ");
        final long start = System.currentTimeMillis();
        final Set<Formula> minCore = new LinkedHashSet<Formula>(core);
        Solver solver = solver();
        solver.options().setSolver(SATFactory.MiniSat);
        for (Iterator<Formula> itr = minCore.iterator(); itr.hasNext();) {
            Formula f = itr.next();
            Formula noF = Formula.TRUE;
            for (Formula f1 : minCore) {
                if (f != f1)
                    noF = noF.and(f1);
            }
            if (solver.solve(noF, bounds).instance() == null) {
                itr.remove();
            }
        }
        final long end = System.currentTimeMillis();
        if (minCore.size() == core.size()) {
            System.out.println("minimal (" + (end - start) + " ms).");
            return true;
        } else {
            System.out.println("not minimal (" + (end - start) + " ms). The minimal core has these " + minCore.size() + " formulas:");
            for (Formula f : minCore) {
                System.out.println(" " + f);
            }
            return false;
        }
    }

    /**
     * Checks that the given core is unsatisfiable with respect to the given bounds.
     *
     * @return true if the core is correct; false otherwise
     */
    static boolean checkCorrect(Set<Formula> core, Bounds bounds) {
        System.out.print("checking correctness ... ");
        final long start = System.currentTimeMillis();
        Solver solver = solver();
        solver.options().setSolver(SATFactory.MiniSat);
        final Solution sol = solver.solve(Formula.and(core), bounds);
        final long end = System.currentTimeMillis();
        if (sol.instance() == null) {
            System.out.println("correct (" + (end - start) + " ms).");
            return true;
        } else {
            System.out.println("incorrect! (" + (end - start) + " ms). The core is satisfiable:");
            System.out.println(sol);
            return false;
        }
    }

    /**
     * @return strategy with the given name
     */
    @SuppressWarnings("unchecked" )
    private static Class< ? extends ReductionStrategy> findStrategy(String className) {
        try {
            final Class< ? > c = Class.forName(className);
            if (ReductionStrategy.class.isAssignableFrom(c))
                return (Class<ReductionStrategy>) c;
            else {
                throw new IllegalArgumentException(className + " is not a known strategy.");
            }
        } catch (ClassNotFoundException e) {
            throw new IllegalArgumentException(className + " is not a known strategy.");
        }
    }

    /**
     * @return scope specification corresponding to the given string
     */
    private static int scope(String scope) {
        int ret;
        try {
            ret = Integer.parseInt(scope);
        } catch (NumberFormatException n) {
            ret = -1;
        }
        if (ret <= 0) {
            throw new IllegalArgumentException(scope + " is not a valid scope.");
        }
        return ret;
    }

    private static Map<String,String> processOptionalArgs(String[] args) {
        final Map<String,String> ret = new LinkedHashMap<String,String>();
        for (int i = 2; i < args.length;) {
            if (!ret.containsKey(args[i]))
                if (i + 1 < args.length && !args[i + 1].startsWith("-")) {
                    ret.put(args[i], args[i + 1]);
                    i += 2;
                } else {
                    ret.put(args[i], "");
                    i++;
                }
            else {
                usage();
            }
        }
        return ret;
    }

    private static Solver solver() {
        final Solver solver = new Solver();
        solver.options().setBitwidth(8);
        solver.options().setSolver(SATFactory.MiniSatProver);
        solver.options().setLogTranslation(1);
        return solver;
    }

    /**
     * Usage: java tests.benchmarks.UCoreStats <class> <scope> [-m method] [-s
     * strategy | oce] [-d depth] [-o (user | stats) ]
     */
    private static void usage() {
        System.out.println("Usage: java tests.benchmarks.UCoreStats <class> <scope> [-m method] [-s strategy | oce] [-d depth] [-o (user | stats) ]");
        System.exit(2);
    }

    /**
     * Runs the minimal core finder using the specified strategy (with the given
     * resolution depth, if applicable) on the given methods, bounds, and prints out
     * results using the given results printer.
     */
    private static void findMinCore(final Class< ? extends ReductionStrategy> strategy, final int depth, final Map<Method,Formula> checks, final Bounds bounds, final ResultPrinter out) {

        try {

            final Solver solver = solver();
            final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
            bean.setThreadCpuTimeEnabled(true);
            for (Map.Entry<Method,Formula> check : checks.entrySet()) {
                // System.out.println(PrettyPrinter.print(check.getValue(), 1));
                Solution sol = solver.solve(check.getValue(), bounds);

                if (sol.outcome() == Solution.Outcome.UNSATISFIABLE) {

                    final long start = bean.getCurrentThreadUserTime() / 1000000;
                    final Set<Formula> initialCore = Nodes.minRoots(check.getValue(), sol.proof().highLevelCore().values());
                    final Set<Formula> minCore;

                    if (strategy == null) { // no strategy -- one-step
                        minCore = initialCore;
                    } else {
                        if (strategy.getSimpleName().startsWith("RCE")) {
                            sol.proof().minimize(strategy(strategy, sol.proof().log(), depth));
                        } else {
                            sol.proof().minimize(strategy(strategy, sol.proof().log()));
                        }
                        minCore = Nodes.minRoots(check.getValue(), sol.proof().highLevelCore().values());
                    }
                    final long end = bean.getCurrentThreadUserTime() / 1000000;

                    out.printUnsat(check.getKey().getName(), check.getValue(), bounds, sol.stats(), initialCore, minCore, end - start);

                    assert checkCorrect(minCore, bounds);
                    assert checkMinimal(minCore, bounds);

                } else if (sol.outcome() == Solution.Outcome.TRIVIALLY_UNSATISFIABLE) {

                    out.printFalse(check.getKey().getName(), check.getValue(), bounds, sol);

                } else {
                    out.printSat(check.getKey().getName(), check.getValue(), bounds, sol);
                }

            }
        } catch (IllegalArgumentException e) {
            System.out.println(e.getMessage());
            usage();
        }
    }

    /**
     * Returns a fresh instance of the given class.
     *
     * @requires the class has a no-argument constructor
     * @return a fresh instance of the given class
     */
    public static Object instance(Class< ? > c) {
        try {
            return c.newInstance();
        } catch (InstantiationException e) {
            throw new IllegalArgumentException(c.getName() + " has no accessible nullary constructor.");
        } catch (IllegalAccessException e) {
            throw new IllegalArgumentException(c.getName() + " has no accessible nullary constructor.");
        }
    }

    /**
     * Usage: java tests.benchmarks.UCoreStats <class> <scope> [-m method] [-s
     * strategy | oce] [-d depth] [-o (user | stats) ]
     */
    public static void main(String[] args) {
        if (args.length < 2)
            usage();
        final Class< ? > problem = findClass(args[0]);
        final Map<String,String> optional = processOptionalArgs(args);

        final Object instance = instance(problem);
        final Bounds bounds = bounds(instance, scope(args[1]));
        final Map<Method,Formula> checks = invokeAll(instance, optional.containsKey("-m") ? Collections.singleton(formulaCreator(problem, optional.get("-m"))) : checks(problem));

        if (checks.isEmpty()) {
            usage();
        }

        final String extractor;
        final Class< ? extends ReductionStrategy> strategy;
        if (optional.containsKey("-s")) {
            extractor = optional.get("-s");
            if (extractor.equals("rce")) {
                strategy = findStrategy("kodkod.engine.ucore.RCEStrategy");
            } else if (extractor.equals("sce")) {
                strategy = findStrategy("kodkod.engine.ucore.SCEStrategy");
            } else if (extractor.equals("nce")) {
                strategy = findStrategy("kodkod.engine.ucore.NCEStrategy");
            } else if (!extractor.equals("oce")) {
                strategy = findStrategy(optional.get("-s"));
            } else {
                strategy = null;
            }
        } else {
            extractor = "oce";
            strategy = null;
        }

        final ResultPrinter out = "stats".equals(optional.get("-o")) ? ResultPrinter.STATS : ResultPrinter.USER;

        if (optional.containsKey("-d")) {
            try {
                // findMinCore(strategy, Integer.parseInt(optional.get("-d")),
                // checks, bounds(instance, 2), out);
                findMinCore(strategy, Integer.parseInt(optional.get("-d")), checks, bounds, out);
            } catch (NumberFormatException nfe) {
                usage();
            }
        } else {
            findMinCore(strategy, Integer.MAX_VALUE, checks, bounds, out);
        }

    }

    /** @return short string representing a given outcome */
    static String outcome(Solution.Outcome outcome) {
        switch (outcome) {
            case SATISFIABLE :
                return "S";
            case UNSATISFIABLE :
                return "U";
            case TRIVIALLY_SATISFIABLE :
                return "T";
            case TRIVIALLY_UNSATISFIABLE :
                return "F";
            default :
                throw new AssertionError("unreachable");
        }
    }

    private static enum ResultPrinter {

                                       USER {

                                           void print(String check, Formula formula, Bounds bounds, Solution.Outcome outcome, Statistics stats) {
                                               System.out.println(check + ": " + outcome);
                                               System.out.println("p cnf " + stats.variables() + " " + stats.clauses());
                                               System.out.println("translation time: " + stats.translationTime() + " ms");
                                               System.out.println("solving time: " + stats.solvingTime() + " ms");
                                           }

                                           @Override
                                           void printSat(String check, Formula formula, Bounds bounds, Solution sol) {
                                               print(check, formula, bounds, sol.outcome(), sol.stats());
                                               System.out.println("instance: " + sol.instance());
                                           }

                                           @Override
                                           void printFalse(String check, Formula formula, Bounds bounds, Solution sol) {
                                               print(check, formula, bounds, sol.outcome(), sol.stats());
                                               System.out.println("trivial core:");
                                               for (Node f : sol.proof().highLevelCore().values()) {
                                                   System.out.println(PrettyPrinter.print(f, 2, 100));
                                               }
                                           }

                                           @Override
                                           void printUnsat(String check, Formula formula, Bounds bounds, Statistics stats, Set<Formula> initialCore, Set<Formula> minCore, long minTime) {
                                               print(check, formula, bounds, Solution.Outcome.UNSATISFIABLE, stats);
                                               System.out.println("formulas: " + Nodes.roots(formula).size());
                                               System.out.println("initial core: " + initialCore.size());
                                               System.out.println("minimized core with " + minCore.size() + " formulas found in " + minTime + " ms:");
                                               for (Formula f : minCore) {
                                                   System.out.println(PrettyPrinter.print(f, 2, 100));
                                               }
                                           }
                                       },
                                       STATS {

                                           void print(String check, Formula formula, Bounds bounds, Solution.Outcome outcome, Statistics stats) {
                                               System.out.print(check);
                                               System.out.print("\t");
                                               System.out.print(outcome(outcome));
                                               System.out.print("\t");
                                               System.out.print(stats.variables());
                                               System.out.print("\t");
                                               System.out.print(stats.clauses());
                                               System.out.print("\t");
                                               System.out.print(stats.translationTime());
                                               System.out.print("\t");
                                               System.out.print(stats.solvingTime());
                                           }

                                           @Override
                                           void printSat(String check, Formula formula, Bounds bounds, Solution sol) {
                                               print(check, formula, bounds, sol.outcome(), sol.stats());
                                               System.out.println();
                                           }

                                           @Override
                                           void printFalse(String check, Formula formula, Bounds bounds, Solution sol) {
                                               print(check, formula, bounds, sol.outcome(), sol.stats());
                                               System.out.print("\t");
                                               System.out.println(sol.proof().highLevelCore().size());
                                           }

                                           @Override
                                           void printUnsat(String check, Formula formula, Bounds bounds, Statistics stats, Set<Formula> initialCore, Set<Formula> minCore, long minTime) {
                                               print(check, formula, bounds, Solution.Outcome.UNSATISFIABLE, stats);
                                               System.out.print("\t");
                                               System.out.print(Nodes.roots(formula).size());
                                               System.out.print("\t");
                                               System.out.print(initialCore.size());
                                               System.out.print("\t");
                                               System.out.print(minCore.size());
                                               System.out.print("\t");
                                               System.out.print(minTime);
                                               System.out.println();
                                           }
                                       };

        abstract void printSat(String check, Formula formula, Bounds bounds, Solution sol);

        abstract void printUnsat(String check, Formula formula, Bounds bounds, Statistics stats, Set<Formula> initialCore, Set<Formula> minCore, long minTime);

        abstract void printFalse(String check, Formula formula, Bounds bounds, Solution sol);
    }

}
