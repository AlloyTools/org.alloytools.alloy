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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;

import tests.util.ProcessRunner;

/**
 * Calls BenchmarkSymmStats on all problems in examples.tptp.* and most problems
 * in examples.* The output is printed in the following (tab separated) format:
 * <class name> <method name> <partial model (bits)> <state space (bits)> <gbp
 * (ms)> <gbp (symms)> <gad (ms)> <gad (symms)> <SAT|UNSAT> <solve+sbp (ms)>
 * <solve (ms)>
 *
 * @author Emina Torlak
 */
public final class BenchmarkSymmStatsDriver extends BenchmarkDriver {

    /**
     * <class name> <method name> <partial model (bits)> <gbp (ms)> <gbp (symms)>
     * <gad (ms)> <gad (symms)> \t
     */
    private static void runSymms(Problem problem) {
        final String cmd = "java -Xmx2G -cp bin tests.benchmarks.BenchmarkSymmStats " + problem.problem + " " + problem.spec + " " + problem.bounds;

        final ProcessRunner runner = new ProcessRunner(cmd.split("\\s"));
        runner.start();
        try {
            runner.join();
            final BufferedReader out;
            out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
            System.out.print(out.readLine());
            out.close();
        } catch (InterruptedException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        } finally {
            runner.destroyProcess();
        }
    }

    /**
     * <state space (bits)> <SAT|UNSAT> <solve with symms (ms)> \t
     */
    private static void runSolveWithSymms(Problem problem) {
        final String cmd = "java -Xmx2G -cp bin tests.benchmarks.BenchmarkStats " + problem.problem + " " + problem.spec + " -scope=" + problem.bounds;

        final ProcessRunner runner = new ProcessRunner(cmd.split("\\s"));
        runner.start();
        try {
            runner.join();
            final BufferedReader out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
            final String line = out.readLine();
            final String[] data = line.split("\\s");
            if (data.length != 10)
                throw new RuntimeException("badly formatted output: " + line);
            // <class name> <method name> <universe size> <S|U> <translation
            // time (ms)> <# of gates> <# of primary vars> <# of vars> <# of
            // clauses> <solving time (ms)>
            System.out.print(data[6] + "\t");
            System.out.print(data[3].startsWith("S") ? "SAT\t" : "UNSAT\t");
            System.out.print(data[9] + "\t");
            out.close();
        } catch (InterruptedException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        } finally {
            runner.destroyProcess();
        }
    }

    /**
     * <solve no symms (ms)> \n
     */
    private static void runSolveNoSymms(Problem problem) {
        final String cmd = "java -Xmx2G -cp bin tests.benchmarks.BenchmarkStats " + problem.problem + " " + problem.spec + " -scope=" + problem.bounds + " -symm=" + 0;
        final ProcessRunner runner = new ProcessRunner(cmd.split("\\s"));
        runner.start();
        try {
            runner.join(FIVE_MIN);

            if (runner.getState() != Thread.State.TERMINATED) {
                runner.interrupt();
                System.out.println("t\\o");
                runner.destroyProcess();
            } else {
                final BufferedReader out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
                final String line = out.readLine();
                final String[] data = line.split("\\s");
                System.out.println(data.length == 10 ? data[9] : "t\\o");
                out.close();
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (UnsupportedEncodingException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        } finally {
            runner.destroyProcess();
        }
    }

    /**
     * Usage: java tests.benchmarks.BenchmarksSymmStatsDriver
     */
    public static void main(String args[]) {

        System.out.print("class\t");
        System.out.print("method\t");
        System.out.print("partial model (bits)\t");
        System.out.print("gbp (ms)\t");
        System.out.print("gbp (symms)\t");
        System.out.print("gad (ms)\t");
        System.out.print("gad (symms)\t");
        System.out.print("state space (bits)\t");
        System.out.print("sat | unsat\t");
        System.out.print("solve+sbp (ms)\t");
        System.out.println("solve (ms)");

        for (Problem problem : problems) {
            runSymms(problem); // System.out.println();
            runSolveWithSymms(problem);
            runSolveNoSymms(problem);
        }

        final Problem[] graphProblems = {
                                         new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/mulsol.i.1.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/mulsol.i.2.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/mulsol.i.3.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/mulsol.i.4.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/mulsol.i.5.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/school1_nsh.col,DIMACS,13)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/school1.col,DIMACS,13)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/zeroin.i.1.col,DIMACS,27)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/zeroin.i.2.col,DIMACS,28)", "coloring"), new Problem("examples.classicnp.GraphColoring(/Users/emina/Documents/workspace/relations5/src/examples/classicnp/zeroin.i.3.col,DIMACS,27)", "coloring"),
        };

        for (Problem problem : graphProblems) {
            runSymms(problem); // System.out.println();
            runSolveWithSymms(problem);
            runSolveNoSymms(problem);
        }

    }
}
