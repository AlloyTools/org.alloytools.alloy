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
import java.io.UnsupportedEncodingException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.math.BigInteger;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solver;
import kodkod.engine.config.AbstractReporter;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.util.ints.ArrayIntVector;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntVector;
import tests.util.ProcessRunner;

/**
 * Executes a single problem. The output is printed in the following (tab
 * separated) format: <class name> <method name> <partial model bits> <gbp (ms)>
 * <gbp (symms)> <gad (ms)> <gad (symms)>
 *
 * @author Emina Torlak
 */
public class BenchmarkSymmStats {

    private static void usage() {
        System.out.println("Usage: java tests.benchmarks.BenchmarkSymmStats <class name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] [<class name>[(<primitive | string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive | string | enum>[,<primitive | string | enum>]*)]]");
        System.exit(1);
    }

    private static final ThreadMXBean bean = ManagementFactory.getThreadMXBean();
    static {
        bean.setThreadCpuTimeEnabled(true);
    }

    private static class SymmReporter extends AbstractReporter {

        long   gbpTime;
        int[]  symms;
        Bounds bounds;

        @Override
        public void detectingSymmetries(Bounds bounds) {
            this.bounds = bounds.clone();
            gbpTime = bean.getCurrentThreadUserTime();
        }

        @Override
        public void detectedSymmetries(Set<IntSet> parts) {
            final long end = bean.getCurrentThreadUserTime();
            gbpTime = (end - gbpTime) / 1000000;
            symms = new int[parts.size()];
            int i = 0;
            for (IntSet s : parts) {
                symms[i++] = s.size();
            }
        }

        @Override
        public void optimizingBoundsAndFormula() {
            throw new RuntimeException();
        }

        /**
         * Returns a new reporter with its gbpTime, bounds and symms fields initialized
         * with respect to the given formula and bounds.
         */
        static SymmReporter report(Formula formula, Bounds bounds) {
            final SymmReporter reporter = new SymmReporter();
            final Solver solver = new Solver();
            solver.options().setReporter(reporter);
            try {
                solver.solve(formula, bounds);
            } catch (RuntimeException ae) {}
            return reporter;
        }
    }

    private static void toNauty(Bounds bounds, PrintStream stream) {
        int size = bounds.universe().size() + bounds.ints().size();
        for (Relation r : bounds.relations()) {
            final int upsize = bounds.upperBound(r).size(), lowsize = bounds.lowerBound(r).size();
            size += (upsize == lowsize ? upsize : upsize + lowsize) * r.arity();
        }

        stream.println("n=" + size + " $0 *=13 k = 0 " + size + " +d -a -m g");

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
        // stream.println("o");
        stream.println("q");
    }

    private static BigInteger fact(int num) {
        BigInteger ret = new BigInteger("1");
        for (int i = 1; i <= num; i++) {
            ret = ret.multiply(new BigInteger(String.valueOf(i)));
        }
        return ret;
    }

    /**
     * Returns the number of symmetries defined by the given partitions.
     */
    private static BigInteger symms(int[] parts) {
        BigInteger symms = new BigInteger("1");
        for (int part : parts) {
            symms = symms.multiply(fact(part));
        }
        return symms;
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

    private static void printSymmInfo(Formula formula, Bounds bounds) {

        final SymmReporter reporter = SymmReporter.report(formula, bounds);

        // <partial model bits> <gbp (ms)> <gbp (symms)>
        System.out.print(pmBits(bounds) + "\t");
        System.out.print(reporter.gbpTime + "\t");

        System.out.print(symms(reporter.symms) + "\t");

        // <gad (ms)> <gad (symms)>
        try {
            final long startGen = bean.getCurrentThreadUserTime();
            final File tmp = File.createTempFile("symmgraph", ".txt");
            final PrintStream stream = new PrintStream(new FileOutputStream(tmp));
            toNauty(reporter.bounds, stream);
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
                    return;
                }

                final BufferedReader out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
                String line;

                String allSymms = null;
                long gadTime = -1;

                final Pattern spattern = Pattern.compile(".+grpsize=(.+?);.*");
                final Matcher smatcher = spattern.matcher("");
                final Pattern tpattern = Pattern.compile(".+cpu time = (.+?)\\s.*");
                final Matcher tmatcher = tpattern.matcher("");
                while ((line = out.readLine()) != null) {
                    smatcher.reset(line);
                    if (smatcher.matches()) {
                        allSymms = smatcher.group(1);
                    } else {
                        tmatcher.reset(line);
                        if (tmatcher.matches()) {
                            gadTime = (long) (Double.parseDouble(tmatcher.group(1)) * 1000);
                            if (gadTime == 0)
                                gadTime++;
                        }
                    }
                    // System.out.println(line);
                }
                out.close();

                System.out.print(gadTime < 0 ? "err\t" : (gadTime + (endGen - startGen) / 1000000) + "\t");
                System.out.print(allSymms == null ? "err\t" : allSymms + "\t");

            } catch (InterruptedException e) {
                System.out.println("INTERRUPTED");
            } catch (UnsupportedEncodingException e) {
                e.printStackTrace();
                System.exit(1);
            } finally {
                runner.destroyProcess();
                destroy("dreadnaut");
                tmp.delete();
            }
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    /**
     * Usage: java tests.benchmarks.BenchmarkSymmStats <class name>[(<primitive |
     * string | enum>[,<primitive | string | enum>]*)] <method name>[(<primitive |
     * string | enum>[,<primitive | string | enum>]*)] [<method name>(<primitive |
     * string | enum>[,<primitive | string | enum>]*)]
     */
    public static void main(String[] args) {
        if (args.length != 2 && args.length != 3)
            usage();

        try {

            final Object instance = construct(args[0].contains("(") ? args[0] : args[0] + "()");
            final Formula formula = create(instance, args[1].contains("(") ? args[1] : args[1] + "()");
            final Bounds bounds = create(instance, args.length == 3 ? args[2] : "bounds()");

            // <class name> <method name>
            System.out.print(args[0] + "\t");
            System.out.print(args[1].split("\\(")[0] + "\t");

            // <PURE|EXT> <gbp (ms)> <gbp (symms)> <gad (ms)> <gad (symms)>
            printSymmInfo(formula, bounds);

        } catch (NumberFormatException nfe) {
            usage();
        }
    }
}
