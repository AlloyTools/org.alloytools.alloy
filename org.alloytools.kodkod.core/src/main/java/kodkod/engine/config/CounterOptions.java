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
package kodkod.engine.config;

import java.util.Locale;

/**
 * Stores information about various user-level translation and analysis options.
 * It can be used to choose the Model Counter, control symmetry breaking, etc.
 *
 * @specfield counter_name: String // the name of the model counter to use
 * @specfield mc_result_file: String // the address of the file that stores the
 *            result returned by the model counter
 * @author Jiayi Yang
 */
public final class CounterOptions implements Cloneable {

    /*
     * parameters of the sat solver, which can serve as the reference when we set
     * parameters for model counters private Reporter reporter = new
     * AbstractReporter() {}; private SATFactory solver = SATFactory.DefaultSAT4J;
     * private int symmetryBreaking = 20; private IntEncoding intEncoding =
     * IntEncoding.TWOSCOMPLEMENT; private int bitwidth = 4; private int sharing =
     * 3; private OverflowPolicy ofPolicy = OverflowPolicy.NONE; private boolean
     * allowHOL = false; private boolean holFullIncrements = true; private int
     * holSome4AllMaxIter = -1; private int holFixpointMaxIter = -1; private int
     * skolemDepth = 0; private int logTranslation = 0; private int coreGranularity
     * = 0;
     */

    private String counter_name     = "ApproxMC";
    private String mc_result_file   = null;
    private String cnf_file_addr    = null;
    private String var_file_addr    = null;
    private String binary_directory = null;
    private String os               = null;
    //private String pid_file_addr    = null;

    // [AM]
    public static boolean isDebug() {
        return false; // TODO: read from the environment or something
    }

    /**
     * Constructs a CounterOptions object initialized with default values.
     *
     * @ensures this.counter_name = "ApproxMC" Other parameters: to be added get the
     *          current OS's name
     */
    public CounterOptions() {
        String os = System.getProperty("os.name").toLowerCase(Locale.US).replace(' ', '-').toLowerCase();
        if (os.startsWith("mac-"))
            os = "mac";
        else if (os.startsWith("windows-"))
            os = "windows";
        this.os = os;
    }

    /**
     * Sets the counter's name to the given value.
     *
     * @ensures this.counter_name = counter_name
     * @throws NullPointerException counter_name = null
     */
    public void setCounterName(String counter_name) {
        if (counter_name == null)
            throw new NullPointerException();
        this.counter_name = counter_name;
    }

    /**
     * Returns the name of the model counter. The default is "ApproxMC".
     *
     * @return this.counter_name
     */
    public String counterName() {
        return this.counter_name;
    }

    /**
     * Sets the result file's address to the given value.
     *
     * @ensures this.mc_result_file = mc_result_file
     * @throws NullPointerException mc_result_file = null
     */
    public void setResultAddr(String mc_result_file) {
        if (mc_result_file == null)
            throw new NullPointerException();
        this.mc_result_file = mc_result_file;
    }

    /**
     * Returns the result file's address.
     *
     * @return this.mc_result_file
     */
    public String resultAddr() {
        return this.mc_result_file;
    }

    /**
     * Sets the cnf file's address to the given value.
     *
     * @ensures this.cnf_file_addr = cnf_file_addr
     * @throws NullPointerException cnf_file_addr = null
     */
    public void setCNFAddr(String cnf_file_addr) {
        if (cnf_file_addr == null)
            throw new NullPointerException();
        this.cnf_file_addr = cnf_file_addr;
    }

    /**
     * Returns the CNF file's address.
     *
     * @return this.cnf_file_addr
     */
    public String CNFAddr() {
        return this.cnf_file_addr;
    }

    /**
     * Sets the binary directory's address to the given value.
     *
     * @ensures this.binary_directory = binary_directory
     * @throws NullPointerException binary_directory = null
     */
    public void setBinaryDirectory(String binary_directory) {
        if (binary_directory == null)
            throw new NullPointerException();
        this.binary_directory = binary_directory;
    }

    /**
     * Returns the binary directory's address.
     *
     * @return this.binary_directory
     */
    public String binaryDirectory() {
        return this.binary_directory;
    }

    /**
     * Sets the var file's address to the given value.
     *
     * @ensures this.var_file_addr = var_file_addr
     * @throws NullPointerException var_file_addr = null
     */
    public void setVarAddr(String var_file_addr) {
        if (var_file_addr == null)
            throw new NullPointerException();
        this.var_file_addr = var_file_addr;
    }

    /**
     * Returns the var file's address.
     *
     * @return this.var_file_addr
     */
    public String varAddr() {
        return this.var_file_addr;
    }

    /**
     * Returns the OS's name.
     *
     * @return this.os
     */
    public String OS() {
        return this.os;
    }

    /**
     * Sets the pid file's address to the given value.
     *
     * @ensures this.pid_file_addr = pid_file_addr
     * @throws NullPointerException pid_file_addr = null
     * 
     *             public void setPidFileAddr(String pid_file_addr) { if
     *             (pid_file_addr == null) throw new NullPointerException();
     *             this.pid_file_addr = pid_file_addr; }
     */

    /**
     * Returns the pid file's address.
     *
     * @return this.pid_file_addr
     * 
     *         public String pidAddr() { return this.pid_file_addr; }
     */



    /**
     * Returns a shallow copy of this CounterOptions object. In particular, the
     * returned options shares the same counter's name, the result file's address
     * and the error file's address as this Options.
     *
     * @return a shallow copy of this CounterOptions object.
     */
    @Override
    public CounterOptions clone() {
        final CounterOptions c = new CounterOptions();
        c.setCounterName(this.counter_name);
        c.setResultAddr(this.mc_result_file);
        c.setCNFAddr(this.cnf_file_addr);
        c.setBinaryDirectory(this.binary_directory);
        return c;
    }

    /**
     * Returns a string representation of this CounterOptions object.
     *
     * @return a string representation of this CounterOptions object.
     */
    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("Options:");
        b.append("\n counterName: ");
        b.append(counter_name);
        b.append("\n resultFileAddr: ");
        b.append(mc_result_file);
        b.append("\n CNFFileAddr: ");
        b.append(cnf_file_addr);
        b.append("\n BinaryDirectory: ");
        b.append(binary_directory);
        /*
         * To be updated: other parameters b.append("\n reporter: ");
         * b.append(reporter); b.append("\n intEncoding: "); b.append(intEncoding);
         * b.append("\n bitwidth: "); b.append(bitwidth); b.append("\n sharing: ");
         * b.append(sharing); b.append("\n symmetryBreaking: ");
         * b.append(symmetryBreaking); b.append("\n skolemDepth: ");
         * b.append(skolemDepth); b.append("\n logTranslation: ");
         * b.append(logTranslation); b.append("\n coreGranularity: ");
         * b.append(coreGranularity); b.append("\n noOverflow: "); b.append(ofPolicy);
         * b.append("\n allowHOL: "); b.append(allowHOL);
         * b.append("\n holFullIncrements: "); b.append(holFullIncrements);
         * b.append("\n holSome4AllMaxIter: "); b.append(holSome4AllMaxIter);
         * b.append("\n holFixpointMaxIter: "); b.append(holFixpointMaxIter);
         */
        return b.toString();
    }
}