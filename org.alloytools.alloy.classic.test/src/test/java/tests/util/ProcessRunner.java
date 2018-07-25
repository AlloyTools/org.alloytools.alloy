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
package tests.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

/**
 * A simple thread that runs a given command in a fresh process.
 *
 * @specfield cmd: String[]
 * @author Emina Torlak
 */
public final class ProcessRunner extends Thread {

    private final String[] cmd;
    private Process        process;

    /**
     * Constructs a process runner for the given command.
     *
     * @effects this.cmd' = cmd
     */
    public ProcessRunner(String... cmd) {
        this.cmd = cmd;
        process = null;
    }

    /**
     * Destroys the process wrapped by this thread, if any.
     *
     * @effects destroys the process wrapped by this thread, if any.
     */
    public void destroyProcess() {
        if (process != null) {
            process.destroy();
            process = null;
        }
    }

    /**
     * Gets the input stream of the subprocess running this.com. The stream obtains
     * data piped from the standard output stream of the process run by this thread.
     *
     * @return input stream of the subprocess running this.com
     */
    public InputStream processOutput() {
        if (process == null) {
            System.out.println("process not started.");
            throw new IllegalStateException();
        } else {
            return process.getInputStream();
        }
    }

    /**
     * Gets the output stream of the subprocess running this.com. The stream pipes
     * data to the standard input stream of the process run by this thread.
     *
     * @return output stream of the subprocess running this.com.
     */
    public OutputStream processInput() {
        if (process == null) {
            System.out.println("process not started.");
            throw new IllegalStateException();
        } else {
            return process.getOutputStream();
        }
    }

    /**
     * Gets the error stream of the subprocess running this.com. The stream obtains
     * data piped from the standard error stream of the process run by this thread.
     *
     * @return error stream of the subprocess running this.com
     */
    public InputStream processError() {
        if (process == null) {
            System.out.println("process not started.");
            throw new IllegalStateException();
        } else {
            return process.getErrorStream();
        }
    }

    /**
     * Starts and waits for a process that runs this.cmd
     *
     * @see java.lang.Thread#run()
     */
    @Override
    public void run() {
        try {
            process = Runtime.getRuntime().exec(cmd);
            process.waitFor();
        } catch (IOException e) {
            System.out.print("Could not run: ");
            for (String c : cmd) {
                System.out.print(c + " ");
            }
            System.out.println();
            System.exit(1);
        } catch (InterruptedException e) {
            // ignore
        }
    }
}
