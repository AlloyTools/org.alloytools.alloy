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
package kodkod.engine;

import java.io.File;
import java.io.IOException;
import java.lang.ProcessBuilder.Redirect;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import kodkod.engine.config.CounterOptions;

/**
 * A computational engine for solving model counting problems. It takes the
 * argument of the counter's name, then finds the corresponding executable file
 * for the user's Operating System. The executable file also supports other
 * parameters of the model counter. If the user didn't specify them, the model
 * counter will use the default parameters.
 *
 * @author Jiayi Yang
 */
public final class Counter {

    private final CounterOptions options;

    /**
     * Constructs a new Counter with the default options.
     *
     * @ensures this.options' = new CounterOptions()
     */
    public Counter() {
        this.options = new CounterOptions();

    }

    /**
     * Constructs a new Counter with the given options.
     *
     * @ensures this.options' = options
     * @throws NullPointerException options = null
     */
    public Counter(CounterOptions options) {
        if (options == null)
            throw new NullPointerException();
        this.options = options;
    }

    /**
     * Returns the Options object used by this Counter to guide the model counting
     * process.
     *
     * @return this.options
     */
    public CounterOptions options() {
        return options;
    }

    /**
     *
     * Attempts to solve the model counting problem of the given cnf file and save
     * the result and error information in the given file addresses. To be added :
     * Is there any possibility that the model counter can't give a valid result for
     * the given cnf file?
     *
     * @throws InterruptedException
     * @throws IOException
     *
     * @see CounterOptions
     */
    public void count() throws InterruptedException, IOException {
        // Compute the appropriate platform
        /*
         * String os = System.getProperty("os.name").toLowerCase(Locale.US).replace(' ',
         * '-'); if (os.startsWith("mac-")) os = "mac"; else if
         * (os.startsWith("windows-")) os = "windows"; String arch =
         * System.getProperty("os.arch").toLowerCase(Locale.US).replace(' ', '-'); if
         * (arch.equals("powerpc")) arch = "ppc-" + os; else if (os.equals("mac")) { if
         * (arch.endsWith("64")) { arch = "x64-mac"; } else { arch = "x86-mac"; } } else
         * arch = arch.replaceAll("\\Ai[3456]86\\z", "x86") + "-" + os;
         */

        String cnf_file_addr = options.CNFAddr();
        String var_file_addr = options.varAddr();
        String fs = System.getProperty("file.separator");

        ProcessBuilder pb = null;

        if (options.counterName().equals("ApproxMC")) {
            pb = new ProcessBuilder(options.binaryDirectory() + fs + options.counterName().toLowerCase(), cnf_file_addr);
        } else if (options.counterName().equals("ProjMC")) {
            List<String> command = new ArrayList<>();
            command.add(options.binaryDirectory() + fs + options.counterName().toLowerCase());
            command.add(cnf_file_addr);
            command.add("-fpv=" + var_file_addr);
            pb = new ProcessBuilder(command);
        }

        File outputLog = new File(options.resultAddr());
        pb.redirectErrorStream(true);
        pb.redirectOutput(Redirect.appendTo(outputLog));

        setUpEnvironment(pb);

        Process process;

        process = pb.start();
        //writePidToFile(process.pid());
        process.waitFor();
        //To do: timeout check
    }


    /**
     * {@inheritDoc}
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return options.toString();
    }

    private void setUpEnvironment(ProcessBuilder builder) throws IOException {
        if (this.options().OS().equals("linux") || this.options().OS().equals("mac")) {
            Map<String,String> env = builder.environment();
            String env_var_name = "LD_LIBRARY_PATH";
            if (this.options().OS().equals("mac")) {
                env_var_name = "DYLD_FALLBACK_LIBRARY_PATH";
            }
            env.put(env_var_name, this.options().binaryDirectory());
        }
    }
    /*
     * private void writePidToFile(Long pid) throws IOException { byte[] pid_bytes =
     * (pid + "\n").getBytes(); RandomAccessFile f = new RandomAccessFile(new
     * File(this.options().pidAddr()), "rw"); f.seek(0); f.write(pid_bytes);
     * f.close(); }
     */
}
