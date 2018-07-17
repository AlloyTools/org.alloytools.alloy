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

public class SEConfig {
    public static final String SE_URL_HTTP = "https://solve.satalia.com/api/v2/jobs";

    public static final String URL_SCHEDULE = "schedule";
    public static final String URL_STATUS = "status";
    public static final String URL_RESULTS = "results";
    public static final String URL_STOP = "stop";

    public static final String CODE_JOB_NOT_FOUND = "5";
    public static final String CODE_UNRECOGNISED_KEY = "16";
    public static final String DEFAULT_TIME_LIMIT = "10 minutes";

    public static final String DEFAULT_MODEL_NAME = "myModel";
    public static final String SAT_EXTENSION = ".cnf";
}

