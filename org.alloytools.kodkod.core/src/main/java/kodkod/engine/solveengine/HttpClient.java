package kodkod.engine.solveengine;

import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.lang.reflect.Type;
import java.net.URL;
import java.net.URLDecoder;
import java.net.UnknownHostException;
import java.rmi.ServerException;
import java.util.ArrayList;
import java.util.Base64;
import java.util.concurrent.TimeUnit;

import javax.json.bind.Jsonb;
import javax.json.bind.JsonbBuilder;
import javax.json.bind.spi.JsonbProvider;
import javax.net.ssl.HttpsURLConnection;

import kodkod.engine.solveengine.enums.SEStatusCode;

public class HttpClient {

    /** Containing the problem to solve. */
    private Model        model;
    /** Number of seconds to wait between each fetchStatus request */
    private int          sleepTimeSeconds;
    /**
     * The id of the job that is created when the problem is sent to SolveEngine
     * Allows to retrieve the problem being solved
     */
    private String       jobId;
    /**
     * Booleans to figure out if this instance has already been launched but stopped
     * before the end
     */
    private boolean      jobCreated   = false;
    private boolean      jobScheduled = false;
    private boolean      jobDone      = false;
    /** Updated status of the job processing the problem */
    private SEStatusCode seStatus     = SEStatusCode.NOTSTARTED;

    public int getSleepTimeSeconds() {
        return sleepTimeSeconds;
    }

    public String getJobId() {
        return jobId;
    }

    public void setJobId(String jobId) {
        this.jobId = jobId;
    }

    public SEStatusCode getSeStatus() {
        return seStatus;
    }

    public void setSeStatus(SEStatusCode seStatus) {
        this.seStatus = seStatus;
    }

    public HttpClient(Model model, int sleepTime) {
        this.model = model;
        this.sleepTimeSeconds = sleepTime;
        this.jobId = "";
    }

    /**
     * Do the whole process for solving a problem using the online solver at
     * solve.satalia.com
     *
     * @return the result of the problem formatted in an Helper.SEResults instance
     * @throws SolvingStoppedException if the online solver stopped before ending
     *             the job
     * @throws UnusualResponseException if the status received is not usual
     * @throws ServerException if the response got from an https request is
     *             unexpected
     * @throws UnsupportedEncodingException if Java fails to encode the problem,
     *             should not happen
     * @throws InvalidTokenException if the token provided is not recognised as
     *             valid by SolveEngine
     * @throws UnknownHostException if there is no internet connection
     */
    public Helper.SEResults solve() throws SolvingStoppedException, UnusualResponseException, ServerException, UnsupportedEncodingException, InvalidTokenException, UnknownHostException, UnsupportedOperationException {
        if (!this.jobCreated) {
            this.createJob();
            this.jobCreated = true;
        }

        if (!this.jobScheduled) {
            this.scheduleJob();
        }

        if (!this.jobDone) {
            this.setSeStatus(this.waitResults());
        }

        return this.fetchSolutions();
    }

    /**
     * Encodes the problem data in base 64, then sends it to solve.satalia.com, with
     * the api-key, to create a job (that will be solving the problem when
     * scheduled)
     *
     * @throws UnsupportedEncodingException if Java fails to encode the problem,
     *             should not happen
     * @throws ServerException if the response got from the request is unexpected
     * @throws UnknownHostException if there is no internet connection
     * @throws InvalidTokenException if the token provided is not recognised as
     *             valid by SolveEngine
     * @throws UnsupportedOperationException if Java fails to encode the cnf text of
     *             the problem, should not happen
     */
    private void createJob() throws UnsupportedEncodingException, ServerException, InvalidTokenException, UnknownHostException, UnsupportedOperationException {

        String encoded = null;
        encoded = Base64.getEncoder().encodeToString(this.model.buildStrModel().getBytes());

        ArrayList<Helper.SEProblem> pbs = new ArrayList<>();
        pbs.add(new Helper.SEProblem(model.getFileName(), URLDecoder.decode(encoded, "utf-8")));

        Helper.ProblemsToSend toSend = new Helper.ProblemsToSend(pbs);

        Jsonb jsonb = JsonbProvider.provider().create().build();
        String data = jsonb.toJson(toSend);

        this.model.printIfInteractive("Creating Solve Engine job...");

        Helper.JobCreateResponse resp = (Helper.JobCreateResponse) this.sendRequest("POST", "", false, data, Helper.JobCreateResponse.class);

        if (resp.message.length() > 0) {
            if (resp.code.equals(SEConfig.CODE_UNRECOGNISED_KEY))
                throw new InvalidTokenException("You are using this api-key: " + this.model.getToken() + "\nIt is not recognised. Please check it by signing in at solve.satalia.com, " + "and update it by selecting another solver and then select SolveEngine again");
            throw new ServerException(resp.buildErrorMessage());
        }

        this.model.setJobId(resp.id);
        this.setJobId(resp.id);
    }

    /**
     * Sends a request to schedule a job created precedently. This will actually
     * launch the solver.
     *
     * @throws ServerException if the response got from the request is unexpected
     * @throws UnknownHostException if there is no internet connection
     */
    private void scheduleJob() throws ServerException, UnknownHostException {
        this.model.printIfInteractive("Scheduling Solve Engine job...");

        Helper.SimpleResponse resp = this.sendRequest("POST", SEConfig.URL_SCHEDULE, true, "", Helper.SimpleResponse.class);

        if (resp.message.length() > 0) {
            throw new ServerException(resp.buildErrorMessage());
        }
    }

    /**
     * Sends a request every {@link #sleepTimeSeconds} (2sec by default) to get the
     * status of the solver.
     *
     * @return the status once it is not
     * @throws SolvingStoppedException if the online solver stopped before ending
     *             the job
     * @throws UnusualResponseException if the status received is not usual
     * @throws ServerException if an error occurred in the request and the response
     *             is not understood
     * @throws UnknownHostException if there is no internet connection ,basically
     */
    private SEStatusCode waitResults() throws SolvingStoppedException, UnusualResponseException, ServerException, UnknownHostException {
        Integer secCnt = 0;

        while (true) {

            SEStatusCode seStatus = SEStatusCode.build(this.fetchStatus());

            String msg = new StringBuffer().append("Solving the problem, status : ").append(seStatus).append(" - waiting time : ").append(secCnt.toString()).append("s").toString();
            this.model.printIfInteractive(msg);

            if (seStatus == SEStatusCode.COMPLETED) {
                break;
            } else if (seStatus == SEStatusCode.FAILED) {
                throw new SolvingStoppedException("Error with Solve engine : problem solving failed");
            } else if (seStatus == SEStatusCode.TIMEOUT) {
                throw new SolvingStoppedException(new StringBuffer().append("Error with Solve engine : the time limit (").append(SEConfig.DEFAULT_TIME_LIMIT).append(" by default) has been reached before solving the problem").toString());
            } else if (seStatus == SEStatusCode.STOPPED) {
                throw new SolvingStoppedException("Error with Solve engine : the job has been manually cancelled");
            } else if (seStatus == SEStatusCode.UNKNOWN) {
                throw new UnusualResponseException("Error with Solve engine : the server returned an unknown status");
            }

            try {
                TimeUnit.SECONDS.sleep(this.sleepTimeSeconds);
            } catch (InterruptedException e) {}
            secCnt += this.sleepTimeSeconds;

        }

        return seStatus;
    }

    /**
     * Sends a request to get the status of the sovler solving the problem
     *
     * @return the status of the solver, in a string format
     * @throws ServerException if the response got from the request is unexpected
     * @throws UnknownHostException if there is no internet connection
     */
    private String fetchStatus() throws ServerException, UnknownHostException {
        Helper.JobStatusResponse resp = (Helper.JobStatusResponse) this.sendRequest("GET", SEConfig.URL_STATUS, true, "", Helper.JobStatusResponse.class);

        if (resp.message.length() > 0) {
            if (resp.code.equals(SEConfig.CODE_JOB_NOT_FOUND))
                throw new ServerException("Internal error: SolveEngine seems to have lost the job.");
            throw new ServerException(resp.buildErrorMessage());
        }

        return resp.status;
    }

    /**
     * Sends a request to fetch the solution of the problem
     *
     * @return a SEResults object, containing the results
     */
    private Helper.SEResults fetchSolutions() throws ServerException, UnknownHostException {
        Helper.JobResultsResponse resp = (Helper.JobResultsResponse) this.sendRequest("GET", SEConfig.URL_RESULTS, true, "", Helper.JobResultsResponse.class);

        if (resp.message.length() > 0) {
            throw new ServerException(resp.buildErrorMessage());
        }
        String current_id = resp.job_id;

        if (!current_id.equals(this.jobId)) {
            throw new ServerException("Wrong Job_ID, Server Error");
        }
        return resp.result;
    }

    /**
     * Sends a request to stop a job
     */
    private void stopJob() throws ServerException, UnknownHostException {
        Helper.SimpleResponse resp = this.sendRequest("DELETE", SEConfig.URL_STOP, true, "", Helper.SimpleResponse.class);

        if (resp.message.length() > 0) {
            throw new ServerException(resp.buildErrorMessage());
        }
    }

    /**
     * Sends an https request with a baseUrl solve.satalia.com/api/v2/jobs, with
     * json-formatted data
     *
     * @param msgType "POST", "GET"..
     * @param path the url to add to the baseUrl
     * @param withJobId true if we add the jobId to the url
     * @param data the data to send, in json format
     * @param respModel the class of the expected response
     * @return an object of the type respModel, built using Gson
     * @throws ServerException if the request processing goes wrong
     * @throws UnknownHostException if there is no internet connection
     */
    public Helper.SimpleResponse sendRequest(String msgType, String path, boolean withJobId, String data, Type respModel) throws ServerException, UnknownHostException {
        String toAdd = withJobId ? "/" + this.jobId : "";

        String strUrl = new StringBuffer().append(SEConfig.SE_URL_HTTP).append(toAdd).append("/").append(path).toString();

        HttpsURLConnection con = null;

        try {
            //Create connection
            URL url = new URL(strUrl);
            con = (HttpsURLConnection) url.openConnection();
            con.setRequestMethod(msgType);
            con.setRequestProperty("Content-Type", "application/json");
            con.setRequestProperty("Authorization", "api-key " + this.model.getToken());
            con.setDoOutput(true);

            //Send request
            if (data.length() > 0) {
                DataOutputStream wr = new DataOutputStream(con.getOutputStream());
                wr.writeBytes(data);
                wr.close();
            }

            //Get Response
            InputStream is;
            if (con.getResponseCode() == 200)
                is = con.getInputStream();
            else
                is = con.getErrorStream();

            BufferedReader rd = new BufferedReader(new InputStreamReader(is));
            StringBuilder response = new StringBuilder(); // or StringBuffer if Java version 5+
            String line;
            while ((line = rd.readLine()) != null) {
                response.append(line);
                response.append(System.getProperty("line.separator"));
            }
            rd.close();

            Jsonb jsonb = JsonbBuilder.create();

            return jsonb.fromJson(response.toString(), respModel);
        } catch (UnknownHostException e) {
            throw new UnknownHostException("Could not reach solve.satalia.com. Please check your internet connection.");
        } catch (Exception e) {
            throw new ServerException(e.toString());
        } finally {
            if (con != null) {
                con.disconnect();
            }
        }
    }
}

