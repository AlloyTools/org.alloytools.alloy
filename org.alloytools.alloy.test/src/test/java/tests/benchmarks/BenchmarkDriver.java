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

import static tests.util.Reflection.checks;
import static tests.util.Reflection.findClass;

/**
 * Common code for benchmark drivers
 *
 * @author Emina Torlak
 */
abstract class BenchmarkDriver {

    /**
     * Class name, method, and scope of a problem.
     *
     * @author Emina Torlak
     */
    static final class Problem {

        final String problem, spec, bounds;

        Problem(String problem, String spec, int scope) {
            this.problem = problem;
            this.spec = spec;
            this.bounds = "bounds(" + scope + ")";
        }

        Problem(String problem, String spec) {
            this.problem = problem;
            this.spec = spec;
            this.bounds = "bounds()";
        }

        Problem(String problem, String spec, String bounds) {
            this.problem = problem;
            this.spec = spec;
            this.bounds = bounds;
        }

        Problem(String problem, int scope) {
            this.problem = problem;
            this.spec = checks(findClass(problem)).iterator().next().getName();
            this.bounds = "bounds(" + scope + ")";
        }

        Problem(String problem) {
            this.problem = problem;
            this.spec = checks(findClass(problem)).iterator().next().getName();
            this.bounds = "bounds()";
        }
    }

    static final Problem[] problems = {
                                       new Problem("examples.alloy.Trees", 7), new Problem("examples.alloy.Handshake", "runPuzzle", 10), new Problem("examples.alloy.FileSystem", 30), new Problem("examples.alloy.Dijkstra", 20), new Problem("examples.alloy.RingElection", 8), new Problem("examples.alloy.Lists", "checkEmpties", 60), new Problem("examples.alloy.Lists", "checkReflexive", 14), new Problem("examples.alloy.Lists", "checkSymmetric", 8), new Problem("examples.alloy.AbstractWorldDefinitions", "checkA241", 10), new Problem("examples.alloy.AbstractWorldDefinitions", "checkAbOp_total", 10), new Problem("examples.alloy.AbstractWorldDefinitions", "checkAbIgnore_inv", 10), new Problem("examples.alloy.AbstractWorldDefinitions", "checkAbTransfer_inv", 8), new Problem("examples.tptp.ALG212", 7), new Problem("examples.tptp.ALG195"), new Problem("examples.tptp.ALG197"), new Problem("examples.tptp.COM008", 11), new Problem("examples.tptp.GEO091", 10), new Problem("examples.tptp.GEO092", 8), new Problem("examples.tptp.GEO158", 8), new Problem("examples.tptp.GEO159", 8), new Problem("examples.tptp.GEO115", 9), new Problem("examples.tptp.LAT258", 7), new Problem("examples.tptp.MED007", 35), new Problem("examples.tptp.MED009", 35), new Problem("examples.tptp.NUM374", 5), new Problem("examples.tptp.NUM378"), new Problem("examples.tptp.SET943", 7), new Problem("examples.tptp.SET948", 14), new Problem("examples.tptp.SET967", 4), new Problem("examples.tptp.TOP020", 10),
    };

    static long            FIVE_MIN = 300000, ONE_HOUR = 3600000;
}
