/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.engine.satlab;

import java.io.BufferedReader;
import java.io.Closeable;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * An implementation of a wrapper for an external Yices SAT solver, executed in
 * a separate process. Adapted from {@link kodkod.engine.satlab.ExternalSolver}
 * because Yices does not follow the standard wcnf format. Also extends support
 * for targets.
 * 
 * @author Tiago Guimarães // [HASLab] target-oriented model finding
 */
final class PMaxYicesExternal implements WTargetSATSolver {
	private StringBuilder buffer = new StringBuilder();
	private final int capacity = 8192;
	private final boolean deleteTemp;
	private final String executable, inTemp;
	private final String[] options;
	private RandomAccessFile cnf;
	private final BitSet solution;
	private volatile Boolean sat;
	private volatile int vars, clauses;
	private final int max;
	private Map<Integer,Integer> softclauses = new HashMap<Integer,Integer>();  // [HASLab]
	private List<int[]> hardclauses = new ArrayList<int[]>();  // [HASLab]
	
	/**
	 * Constructs an ExternalSolver that will execute the specified binary
	 * with the given options on the {@code inTemp} file.  The {@code inTemp} file 
	 * will be initialized to contain all clauses added to this solver via the 
	 * {@link #addClause(int[])} method.  The solver is assumed to write its output 
	 * to standard out.  The {@code deleteTemp} flag indicates whether the temporary 
	 * files should be deleted when they are no longer needed by this solver.
	 */
	PMaxYicesExternal(String executable, String inTemp, boolean deleteTemp, int max, String... options) {
		this.deleteTemp = deleteTemp;
		this.sat = null;
		this.solution = new BitSet();
		this.vars = 0;
		this.clauses = 0;
		this.max = max;
		this.executable = executable;
		this.inTemp = inTemp;
		// remove empty strings from the options array
		final List<String> nonEmpty = new ArrayList<String>(options.length);
		for(String opt : options) { 
			if (!opt.isEmpty())
				nonEmpty.add(opt);
		}
		this.options = nonEmpty.toArray(new String[nonEmpty.size()]);
	}

	/**
	 * Silently closes the given resource if it is non-null.
	 */
	private static void close(Closeable closeable) {
		try {
			if (closeable!=null)
				closeable.close();
		} catch (IOException e) { } // ignore
	}

	/**
	 * Returns the length, in characters, of the longest possible header
	 * for a cnf file: p cnf Integer.MAX_VALUE Integer.MAX_VALUE
	 * @return the length, in characters, of the longest possible header
	 * for a cnf file: p cnf Integer.MAX_VALUE Integer.MAX_VALUE
	 */
	private static final int headerLength() {
		return String.valueOf(Integer.MAX_VALUE).length()*3 + 9;
	}

	/**
	 * Flushes the contents of the string buffer to the cnf file.
	 */
	private final void flush(){ 
		try {
			cnf.writeBytes(buffer.toString());
		} catch (IOException e) {
			close(cnf);
			throw new SATAbortedException(e);
		} finally {
			buffer.setLength(0);
		}
	}

	/**
	 * {@inheritDoc}
	 * Clauses are added to a buffer instead of directly to the SAT because it 
	 * must be reconstructed at each iteration to update the targets.
	 * @see kodkod.engine.satlab.SATSolver#addClause(int[])
	 */
	public boolean addClause(int[] lits) {
		clauses++;
		hardclauses.add(lits.clone());
		return true;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 */
	public void addVariables(int numVars) {
		if (numVars < 0)
			throw new IllegalArgumentException("vars < 0: " + numVars);
		vars += numVars;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#addTarget(int)
	 */
	public boolean addTarget(int lit) {
		return addWeight(lit, 1);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#addWeight(int,int)
	 */	
	public boolean addWeight(int lit, int weight) {
		clauses++;
		softclauses.put(lit,weight);
		return true;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#free()
	 */
	public synchronized void free() {
		close(cnf);
		if (deleteTemp) {
			(new File(inTemp)).delete();
		}
	}

	/**
	 * Releases the resources used by this external solver.
	 */
	protected final void finalize() throws Throwable {
		super.finalize();
		free();
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public int numberOfClauses() {
		return clauses;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public int numberOfVariables() {
		return vars;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#numberOfTargets()
	 */
	public int numberOfTargets() {
		return softclauses.size(); 
	}

	/**
	 * @ensures |lit| <= this.vars && lit != 0 => this.solution'.set(|lit|, lit>0)
	 * @throws SATAbortedException  lit=0 || |lit|>this.vars
	 */
	private final void updateSolution(int lit) {
		int abs = StrictMath.abs(lit);
		if (abs<=vars && abs>0)
			solution.set(abs-1, lit>0);
		else
			throw new SATAbortedException("Invalid variable value: |" + lit + "| !in [1.."+vars+"]");
	}
	
	

	/**
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */
	public boolean solve() throws SATAbortedException {

		RandomAccessFile file = null;
		try {
			file = new RandomAccessFile(inTemp, "rw");
			file.setLength(0);
		} catch (FileNotFoundException e) {
			throw new SATAbortedException(e);
		} catch (IOException e) {
			close(file);
			throw new SATAbortedException(e);
		}
		this.cnf = file;
		
		// get enough space into the buffer for the cnf header, which will be written last
		buffer = new StringBuilder();
		for(int i = headerLength(); i > 0; i--) {
			buffer.append(" ");
		}
		buffer.append("\n");
		
		// [HASLab] add the target variables as soft clauses
		for (Integer i : softclauses.keySet()) {
			if (buffer.length()>capacity) 
				flush();
			buffer.append(softclauses.get(i));
			buffer.append(" ");
			buffer.append(i);
			buffer.append(" ");
			buffer.append("0\n");
		}
		// [HASLab] add the problem variables as hard clauses
		for (int[] is : hardclauses) {
			if (buffer.length()>capacity) 
				flush();
			buffer.append(max);
			buffer.append(" ");
			for(int lit: is) {
				buffer.append(lit);
				buffer.append(" ");
			}
			buffer.append("0\n");
		}
		
//		if (sat==null) {
			flush();
			Process p = null;
			BufferedReader out = null;
			try {
				cnf.seek(0);
				cnf.writeBytes("p wcnf " + vars + " " + (clauses) + " " + max);
				cnf.close();

				final String[] command = new String[options.length+2];
				command[0] = executable;
				System.arraycopy(options, 0, command, 1, options.length);
				command[command.length-1] = inTemp;
				p = Runtime.getRuntime().exec(command);
				System.out.println(Arrays.asList(command).toString());

				new Thread(drain(p.getErrorStream())).start();
				out = outputReader(p);
				String line = null;
				while((line = out.readLine()) != null) {
					System.out.println(line);
					String[] tokens = line.split("\\s");
					int tlength = tokens.length;
					if (tlength>0) {
//						if (tokens[0].compareToIgnoreCase("s")==0) {
//							if (tlength==3 && tokens[1].compareToIgnoreCase("OPTIMUM")==0 && tokens[2].compareToIgnoreCase("FOUND")==0) {
//								sat = Boolean.TRUE;
//								continue;
//							} else if (tlength==2 && tokens[1].compareToIgnoreCase("UNSATISFIABLE")==0) {
//								sat = Boolean.FALSE;
//								continue;
//							} 
//							throw new SATAbortedException("Invalid " + executable + " output. Line: " + line);
					if (tokens[0].equals("sat")) {
						sat = Boolean.TRUE;
						continue;				
					} else if (tokens[0].equals("cost:")) {
					} else { //if (tokens[0].compareToIgnoreCase("v")==0) {
							int last = vars;
							for(int i = 0; i < last; i++) {
								updateSolution(Integer.parseInt(tokens[i]));
							}
//							int lit = Integer.parseInt(tokens[last]);
//							if (lit!=0) updateSolution(lit);
//							else if (sat!=null) break;
						} // not a solution line or a variable line, so ignore it.
					}
				}
				if (sat==null) {
					throw new SATAbortedException("Invalid " + executable + " output: no line specifying the outcome.");
				}
			} catch (IOException e) {
				throw new SATAbortedException(e);
			} catch (NumberFormatException e) {
				throw new SATAbortedException("Invalid "+ executable +" output: encountered a non-integer variable token.", e);
			} finally {
				close(cnf);
				close(out);
			}
//		}
		return sat;
	}
	
	/**
	 * Returns a runnable that drains the specified input stream.
	 * @return a runnable that drains the specified input stream.
	 */
	private static Runnable drain(final InputStream input) { 
		return new Runnable() {
			public void run() {
				try {
					final byte[] buffer=new byte[8192];
					while(true) {
						int n=input.read(buffer);
						if (n<0) break;
					}
				} catch (IOException ex) {
				} finally {
					close(input);
				}
			}
		};
	}

	/**
	 * Returns a reader for reading the output of the given process.
	 * @return a reader for reading the output of the given process.
	 * @throws IOException
	 */
	private BufferedReader outputReader(Process p) throws IOException {
		try {
			return new BufferedReader(new InputStreamReader(p.getInputStream(), "ISO-8859-1"));
		} catch (IOException e) {
			close(p.getInputStream());
			throw e;
		}
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	public boolean valueOf(int variable) {
		if (!Boolean.TRUE.equals(sat))
			throw new IllegalStateException();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars+"]");
		return solution.get(variable-1);
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return executable + " " + options;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.pardinus.target.TargetOrientedSATSolver#clearTargets(int)
	 */	
	public boolean clearTargets() {
		clauses = clauses - softclauses.size();
		softclauses = new HashMap<Integer, Integer>();
		return Boolean.TRUE.equals(sat);
	}
}
