/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4;

import java.io.InputStream;
import java.util.Timer;
import java.util.TimerTask;

/**
 * This provides a convenience wrapper around a Process object.
 * <p>
 * To launch a subprocess, simply write Subprocess.exec(timeout, args);
 * <p>
 * <b>Thread Safety:</b> Safe.
 */

public final class Subprocess {

    /** Timer used to schedule a timeout for the process. */
    private static final Timer stopper = new Timer();

    /**
     * This field will store the program output (or "" if an error occurred)
     */
    private String             stdout  = null;

    /**
     * This field will store an error message (or "" if no error occurred)
     */
    private String             stderr  = null;

    /**
     * Constructor is private since we only allow the static method exec() to
     * construct objects of this class.
     */
    private Subprocess() {}

    /**
     * Executes the given command line, wait for its completion, then return its
     * output.
     *
     * @param timeLimit - we will attempt to terminate the process after that many
     *            milliseconds have passed
     * @param p - preconstructed Process object
     */
    private static String exec(final long timeLimit, final Process p) throws Exception {
        final Subprocess pro = new Subprocess();
        final InputStream f1 = p.getInputStream(), f2 = p.getErrorStream();
        TimerTask stoptask = new TimerTask() {

            @Override
            public void run() {
                synchronized (pro) {
                    if (pro.stdout != null && pro.stderr != null)
                        return;
                    pro.stdout = "";
                    pro.stderr = "Error: timeout";
                }
                p.destroy();
            }
        };
        synchronized (Subprocess.class) {
            stopper.schedule(stoptask, timeLimit);
        }
        new Thread(new Runnable() {

            @Override
            public void run() {
                String err = null;
                try {
                    if (f2.read() >= 0)
                        err = "Error: stderr";
                } catch (Throwable ex) {
                    err = "Error: " + ex;
                }
                synchronized (pro) {
                    if (err != null) {
                        pro.stdout = "";
                        pro.stderr = err;
                    } else if (pro.stderr == null)
                        pro.stderr = "";
                }
            }
        }).start();
        p.getOutputStream().close();
        StringBuilder output = new StringBuilder();
        byte[] buf = new byte[8192];
        while (true) {
            int n = f1.read(buf);
            if (n < 0)
                break;
            else
                for (int i = 0; i < n; i++)
                    output.append((char) (buf[i]));
        }
        synchronized (pro) {
            if (pro.stdout == null)
                pro.stdout = output.toString();
        }
        for (int i = 0; i < 10; i++) {
            synchronized (pro) {
                if (pro.stderr != null)
                    return pro.stderr + pro.stdout;
            }
            Thread.sleep(500);
        }
        return "Error: wait timeout";
    }

    /**
     * Executes the given command line, wait for its completion, then return its
     * output.
     *
     * @param timeLimit - we will attempt to terminate the process after that many
     *            milliseconds have passed
     * @param commandline - the command line
     */
    public static String exec(final long timeLimit, final String[] commandline) {
        Process p = null;
        try {
            p = Runtime.getRuntime().exec(commandline);
            return exec(timeLimit, p);
        } catch (Throwable ex) {
            return "Error: " + ex;
        } finally {
            if (p != null)
                p.destroy();
        }
    }
}
