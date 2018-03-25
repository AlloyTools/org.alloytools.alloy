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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.ArrayIntVector;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;
import kodkod.util.ints.IntVector;
import kodkod.util.ints.Ints;
import tests.util.ProcessRunner;

/**
 * Executes a single problem. The output is printed in the following (tab
 * separated) format: <class name> <method name> <partial model bits> <symm time
 * (ms)> <# of symms> <state bits> <SAT|UNSAT> <SAT time (ms)>
 *
 * @author Emina Torlak
 */
class BenchmarkSymmStats2 {

    private static void usage() {
        System.out.println("Usage: java tests.BenchmarkSymmStats <GBP|GAD> <class name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] [<class name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string | enum>[,<primitive | string | enum>]*)]]");
        System.exit(1);
    }

    private static final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
    static {
        bean.setThreadCpuTimeEnabled(true);
    }

    private static void toNauty(Bounds bounds, PrintStream stream) {
        int size = bounds.universe().size() + bounds.ints().size();
        for (Relation r : bounds.relations()) {
            final int upsize = bounds.upperBound(r).size(), lowsize = bounds.lowerBound(r).size();
            size += (upsize == lowsize ? upsize : upsize + lowsize) * r.arity();
        }

        stream.println("n=" + size + " $0 *=13 k = 0 " + size + " +d -a g");

        int v = bounds.universe().size();
        final IntVector vec = new ArrayIntVector();
        vec.add(v);
        for (Relation r : bounds.relations()) {
            final int arity = r.arity();
            final TupleSet up = bounds.upperBound(r), down = bounds.lowerBound(r);
            final TupleSet[] sets = up.size() == down.size() || down.size() == 0 ? new TupleSet[] {
                                                                                                   up
            } : new TupleSet[] {
                                down, up
            };
            for (TupleSet s : sets) {
                for (Tuple t : s) {
                    for (int i = 0, max = arity - 1; i < max; i++) {
                        stream.println(v + " : " + (v + 1) + " " + t.atomIndex(i) + ";");
                        v++;
                    }
                    stream.println(v + " : " + t.atomIndex(arity - 1) + ";");
                    v++;
                }
                vec.add(v);
            }
        }
        for (TupleSet s : bounds.intBounds().values()) {
            stream.println(v + " : " + s.iterator().next().atomIndex(0) + ";");
            v++;
            vec.add(v);
        }

        // stream.println(".");
        stream.print("f = [ 0:" + (vec.get(0) - 1));
        for (int i = 1; i < vec.size(); i++) {
            stream.print(" | " + vec.get(i - 1) + ":" + (vec.get(i) - 1));
        }
        stream.println(" ]");
        stream.println("x");
        stream.println("o");
        stream.println("q");
    }

    private static void destroy(String name) {
        try {
            final Process process = Runtime.getRuntime().exec("ps -e");
            process.waitFor();
            final BufferedReader out = new BufferedReader(new InputStreamReader(process.getInputStream(), "ISO-8859-1"));
            final Matcher m = Pattern.compile("(\\d+).*?" + name).matcher("");
            for (String line = out.readLine(); line != null; line = out.readLine()) {
                m.reset(line);
                if (m.find()) {
                    Runtime.getRuntime().exec("kill " + m.group(1)).waitFor();
                    break;
                }
            }
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (InterruptedException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    private static class SymmInfo {

        final Set<IntSet> parts;
        final String      time, symms;

        SymmInfo(Set<IntSet> parts, String time, String symms) {
            this.parts = parts;
            this.time = time;
            this.symms = symms;
        }

        SymmInfo(int size) {
            this.parts = new LinkedHashSet<IntSet>();
            for (int i = 0, max = size; i < max; i++) {
                parts.add(Ints.singleton(i));
            }
            this.time = "t\\o";
            this.symms = "t\\o";
        }
    }

    private static SymmInfo allSymms(Bounds bounds) {
        try {
            final long startGen = bean.getCurrentThreadUserTime();
            final File tmp = File.createTempFile("symmgraph", ".txt");
            final PrintStream stream = new PrintStream(new FileOutputStream(tmp));
            toNauty(bounds, stream);
            stream.close();
            final long endGen = bean.getCurrentThreadUserTime();

            final String cmd = "/Users/emina/Desktop/tools/nauty22/run_dreadnaut " + tmp.getAbsoluteFile();

            final ProcessRunner runner = new ProcessRunner(cmd.split("\\s"));
            runner.start();

            try {

                runner.join(BenchmarkDriver.FIVE_MIN);
                if (runner.getState() != Thread.State.TERMINATED) {
                    System.out.print("t\\o\t");
                    System.out.print("t\\o\t");
                    runner.destroyProcess();
                    destroy("dreadnaut");
                    tmp.delete();
                    return new SymmInfo(bounds.universe().size());
                }

                final BufferedReader out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
                String line;

                String allSymms = null;
                long time = -1;
                final Set<IntSet> parts = new LinkedHashSet<IntSet>();

                final Matcher smatcher = Pattern.compile(".+grpsize=(.+?);.*").matcher("");
                final Matcher tmatcher = Pattern.compile(".+cpu time = (.+?)\\s.*").matcher("");
                final Matcher omatcher = Pattern.compile("invarproc \"adjacencies\"").matcher("");

                while ((line = out.readLine()) != null) {
                    smatcher.reset(line);
                    if (smatcher.matches()) {
                        allSymms = smatcher.group(1);
                    } else {
                        tmatcher.reset(line);
                        if (tmatcher.matches()) {
                            time = (long) (Double.parseDouble(tmatcher.group(1)) * 1000);
                            if (time == 0)
                                time++;
                        } else {
                            omatcher.reset(line);
                            if (omatcher.find()) {
                                break;
                            }
                        }
                    }
                }

                if (line != null) {
                    final StringBuilder builder = new StringBuilder();
                    while ((line = out.readLine()) != null) {
                        builder.append(line);
                    }
                    line = builder.toString();
                    // System.out.println(line);
                    final String[] orbits = line.split(";");
                    final Matcher dmatcher = Pattern.compile("\\s*(\\d+)\\s*").matcher("");
                    for (String n : orbits) {
                        String[] range = n.split(":");
                        if (range.length == 2) {
                            dmatcher.reset(range[0]);
                            dmatcher.matches();
                            final int min = Integer.parseInt(dmatcher.group(1));
                            if (min >= bounds.universe().size())
                                break;
                            dmatcher.reset(range[1]);
                            dmatcher.matches();
                            parts.add(Ints.rangeSet(Ints.range(min, Integer.parseInt(dmatcher.group(1)))));
                        } else {
                            range = n.split("\\s+");
                            final IntSet part = new IntTreeSet();
                            for (int i = 0; i < range.length; i++) {
                                dmatcher.reset(range[i]);
                                if (dmatcher.matches()) {
                                    final int match = Integer.parseInt(dmatcher.group(1));
                                    if (match < bounds.universe().size())
                                        part.add(match);
                                    else
                                        break;
                                }
                            }
                            if (part.isEmpty())
                                break;
                            else
                                parts.add(part);
                        }

                    }
                }

                out.close();
                tmp.delete();
                runner.destroyProcess();

                if (time < 0 || allSymms == null || parts.isEmpty())
                    throw new IllegalStateException();
                return new SymmInfo(parts, String.valueOf(time + (endGen - startGen) / 1000000), allSymms);

            } catch (IOException e) {
                tmp.delete();
                runner.destroyProcess();
                destroy("dreadnaut");
                throw new IllegalStateException(e);
            } catch (InterruptedException e) {
                tmp.delete();
                runner.destroyProcess();
                destroy("dreadnaut");
                e.printStackTrace();
                throw new IllegalStateException(e);
            }
        } catch (IOException e) {
            throw new IllegalStateException(e);
        }
    }

    private static BigInteger fact(int num) {
        BigInteger ret = new BigInteger("1");
        for (int i = 1; i <= num; i++) {
            ret = ret.multiply(new BigInteger(String.valueOf(i)));
        }
        return ret;
    }

    /**
     * Returns the size of the partial model (in bits)
     */
    private static int pmBits(Bounds bounds) {
        int pm = 0;
        for (TupleSet lower : bounds.lowerBounds().values()) {
            pm += lower.size();
        }
        return pm;
    }

    // <symm time (ms)> <# of symms> <state bits> <SAT|UNSAT> <SAT time (ms)>
    private static void printGBP(Formula formula, Bounds bounds) {
        final class SymmReporter extends AbstractReporter {

            long       gbpTime;
            BigInteger symms;

            @Override
            public void detectingSymmetries(Bounds bounds) {
                gbpTime = bean.getCurrentThreadUserTime();
            }

            @Override
            public void detectedSymmetries(Set<IntSet> parts) {
                final long end = bean.getCurrentThreadUserTime();
                gbpTime = (end - gbpTime) / 1000000;
                symms = new BigInteger("1");
                for (IntSet s : parts) {
                    symms = symms.multiply(fact(s.size()));
                }
                // System.out.println(parts);
            }
        }
        ;

        final SymmReporter reporter = new SymmReporter();
        final Solver solver = new Solver();
        solver.options().setBitwidth(8);
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setReporter(reporter);

        final Solution sol = solver.solve(formula, bounds);

        // <gbp (ms)> <gbp (symms)>
        System.out.print(reporter.gbpTime + "\t");
        System.out.print(reporter.symms + "\t");
        // <state bits> <SAT|UNSAT> <SAT time (ms)>
        System.out.print(sol.stats().primaryVariables() + "\t");
        System.out.print(sol.instance() == null ? "UNSAT\t" : "SAT\t");
        System.out.print(sol.stats().solvingTime() + "\t");
    }

    // <symm time (ms)> <# of symms> <state bits> <SAT|UNSAT> <SAT time (ms)>
    private static void printGAD(Formula formula, Bounds bounds) {
        final class SymmReporter extends AbstractReporter {

            String symms, time;
            Bounds bounds;

            @Override
            public void detectingSymmetries(Bounds bounds) {
                this.bounds = bounds.clone();
            }

            @Override
            public void detectedSymmetries(Set<IntSet> parts) {
                parts.clear();
                final SymmInfo allSymms = allSymms(bounds);
                parts.addAll(allSymms.parts);
                symms = allSymms.symms;
                time = allSymms.time;
                // System.out.println(parts);
            }
        }
        ;

        final SymmReporter reporter = new SymmReporter();
        final Solver solver = new Solver();
        solver.options().setBitwidth(8);
        solver.options().setSolver(SATFactory.MiniSat);
        solver.options().setReporter(reporter);

        final Solution sol = solver.solve(formula, bounds);

        // <gbp (ms)> <gbp (symms)>
        System.out.print(reporter.time + "\t");
        System.out.print(reporter.symms + "\t");
        // <state bits> <SAT|UNSAT> <SAT time (ms)>
        System.out.print(sol.stats().primaryVariables() + "\t");
        System.out.print(sol.instance() == null ? "UNSAT\t" : "SAT\t");
        System.out.print(sol.stats().solvingTime() + "\t");
    }

    /**
     * Usage: java tests.BenchmarkSymmStats <GBP|GAD> <class name>[(<primitive |
     * string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive |
     * string | enum>[,<primitive | string | enum>]*)] [(<primitive | string |
     * enum>[,<primitive | string | enum>]*)]
     */
    public static void main(String[] args) {
        if (args.length != 3 && args.length != 4)
            usage();

        try {
            final int method;
            if ("GBP".equals(args[0].toUpperCase())) {
                method = 0;
            } else if ("GAD".equals(args[0].toUpperCase())) {
                method = 1;
            } else {
                method = 2;
                usage();
            }

            final Object instance = construct(args[1].contains("(") ? args[1] : args[1] + "()");
            final Formula formula = create(instance, args[2].contains("(") ? args[2] : args[2] + "()");
            final Bounds bounds = create(instance, "bounds" + (args.length == 4 ? args[3] : "()"));

            // <class name> <method name> <partial model bits>
            System.out.print(args[0].split("\\(")[0] + "\t");
            System.out.print(args[1].split("\\(")[0] + "\t");
            System.out.print(pmBits(bounds) + "\t");

            // <symm time (ms)> <# of symms> <state bits> <SAT|UNSAT> <SAT time
            // (ms)>
            if (method == 0)
                printGBP(formula, bounds);
            else
                printGAD(formula, bounds);
            System.out.println();
        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
