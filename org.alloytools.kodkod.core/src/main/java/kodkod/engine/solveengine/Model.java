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

import kodkod.engine.solveengine.enums.SEStatusCode;
import kodkod.engine.solveengine.enums.SolveStatusCode;

import java.io.UnsupportedEncodingException;
import java.net.UnknownHostException;
import java.rmi.ServerException;

public abstract class Model {
    /** The api-key used by solve engine to recognise the user */
    protected String token;

    /** The name of the problem */
    protected String fileName;

    /** Will print the steps of the process going, if true */
    private Boolean interactiveMode;

    /** Instance of HttpClient used to manage http requests for sovling the problem*/
    protected HttpClient client;

    /** Id of the job, used to retrieve the status of the problem being solved by the online solver*/
    protected String jobId;

    /** Status of the solver solving the problem*/
    protected SEStatusCode seStatus;

    /** Status of the solved problem*/
    protected SolveStatusCode solveStatus;

    public void setJobId(String jobId) {
        this.jobId = jobId;
    }

    public String getFileName() { return fileName; }

    public Integer getSleepTime() { return client.getSleepTimeSeconds(); }

    public String getToken() { return token; }

    public Model(String token, String fileName, Integer sleepTime, Boolean interactiveMode) {
        this.interactiveMode = interactiveMode;
        this.token = token;
        this.setFileName(fileName);
        this.client = new HttpClient(this, sleepTime);
        this.seStatus = SEStatusCode.NOTSTARTED;
        this.jobId = "";
    }

    /**
     * reinitialise jobId, solveStatus and seStatus
     */
    public void reinit() {
        jobId = null;
        solveStatus = SolveStatusCode.NOTSTARTED;
        seStatus = SEStatusCode.NOTSTARTED;
    }

    /**
     * Building the string version of the model, ready to be saved or sent as .lp or .cnf file
     * @return
     * @throws UnsupportedOperationException
     */
    protected abstract String buildStrModel() throws UnsupportedOperationException;

    protected abstract void processResults(Helper.SEResults result);

    /**
     * Calls the httpClient to follow the process of solving the model online
     * @throws SolvingStoppedException if the solver could not solve entirely the problem
     * @throws UnsupportedEncodingException if the cnf string could not be encoded
     * @throws UnusualResponseException if the online platform solve.satalia responded something unusual
     * @throws UnsupportedOperationException if the code has been modified not properly
     * @throws ServerException if we could not understand the response of a request
     * @throws InvalidTokenException if the api-key the user provided is not valid
     * @throws UnknownHostException if there is no internet connection
     */
    public void solve() throws SolvingStoppedException, UnsupportedEncodingException, UnusualResponseException,
            UnsupportedOperationException, ServerException, InvalidTokenException, UnknownHostException {
        Helper.SEResults result = null;
        result = this.client.solve();

        this.seStatus = this.client.getSeStatus();
        this.processResults(result);

        this.printIfInteractive("Solving done: " +
                this.solveStatus.getStrVal());
    }

    protected abstract void setFileName(String fileName);
    public abstract void printResults();

    /**
     * If the user asked for the solving to be interactive, will print what is asked to be
     * @param msg
     */
    void printIfInteractive(String msg) {
        if (this.interactiveMode) {
            System.out.println(msg);
        }
    }
    public Boolean getInteractiveMode() {return interactiveMode;}
    public void setInteractiveMode(Boolean interactiveMode) {this.interactiveMode = interactiveMode;}

}
