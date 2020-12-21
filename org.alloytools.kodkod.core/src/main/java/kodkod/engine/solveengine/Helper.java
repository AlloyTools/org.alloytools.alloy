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
package kodkod.engine.solveengine;

import java.util.ArrayList;

public class Helper {

    public static class SEProblem {
        public String name;
        public String data;

        public SEProblem(String name, String data) {
            this.name = name;
            this.data = data;
        }
    }

    public static class SEResults {
        public String status = "";
        public String objective_value = "no objective value";
        public ArrayList<SEVariable> variables = new ArrayList<>();
    }

    public static class SEVariable {
        public String name = "";
        public double value = 0.0;
    }
    public static class ProblemsToSend {
        public ArrayList<SEProblem> problems = new ArrayList<>();

        public ProblemsToSend(ArrayList<SEProblem> problems) {
            this.problems = problems;
        }
    }

    public static class SimpleResponse {
        public String code = "";
        public String message = "";

        public String buildErrorMessage() {
            return new StringBuffer().append("Error type : ")
                    .append(code).append("\nMessage returned by the server : ")
                    .append(message).toString();
        }
    }

    public static class JobCreateResponse extends SimpleResponse {
        public String id = "";
    }

    public static class JobStatusResponse extends SimpleResponse {
        public String status = "";
    }

    public static class JobResultsResponse extends SimpleResponse {
        public String job_id = "";
        public SEResults result = new SEResults();
    }
}
