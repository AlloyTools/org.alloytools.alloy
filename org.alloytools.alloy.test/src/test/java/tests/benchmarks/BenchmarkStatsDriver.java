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
 * Calls BenchmarkStats on all problems in examples.tptp.* and most problems in
 * examples.*
 *
 * @author Emina Torlak
 */
public final class BenchmarkStatsDriver extends BenchmarkDriver {

    private static void usage() {
        System.out.println("Usage: java tests.benchmarks.BenchmarksStatsDriver <sharing depth>");
        System.exit(0);
    }

    /**
     * Usage: java tests.benchmarks.BenchmarksStatsDriver <sharing depth>
     */
    public static void main(String args[]) {
        if (args.length != 1)
            usage();

        System.out.print("name\t");
        System.out.print("method\t");
        System.out.print("universe\t");
        System.out.print("outcome\t");
        System.out.print("translation (ms)\t");
        System.out.print("gates\t");
        System.out.print("primary vars\t");
        System.out.print("vars\t");
        System.out.print("clauses\t");
        System.out.println("solving time (ms)");

        for (Problem problem : problems) {
            final String cmd = "java -Xmx2G -cp bin tests.benchmarks.BenchmarkStats " + problem.problem + " " + problem.spec + " -scope=" + problem.bounds + " -sharing=" + args[0];

            // System.out.println(cmd);

            final ProcessRunner runner = new ProcessRunner(cmd.split("\\s"));
            runner.start();

            try {
                runner.join(FIVE_MIN);
                if (runner.getState() != Thread.State.TERMINATED) {
                    runner.interrupt();
                    runner.destroyProcess();
                    System.out.print(problem.problem + "\t");
                    System.out.print(problem.spec + "\t");
                    System.out.println("na\tna\tna\tna\tna\tna\tna\tna");
                    continue;
                }

                final BufferedReader out = new BufferedReader(new InputStreamReader(runner.processOutput(), "ISO-8859-1"));
                System.out.println(out.readLine());
            } catch (InterruptedException e) {
                System.out.println("INTERRUPTED");
                runner.destroyProcess();
            } catch (UnsupportedEncodingException e) {
                e.printStackTrace();
                System.exit(1);
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }
    }
}
