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

/**
 * Java wrapper for the Yices PMax-SAT solver.
 * 
 * @author Tiago Guimarães // [HASLab] target-oriented model finding
 */
final class PMaxYicesNative extends NativeSolver implements WTargetSATSolver {

	private boolean makearray;
	protected long array = 0;

	public PMaxYicesNative(){
		super(make());
		makearray = true;
		array = allocArray();
		//System.out.println("new");
		targetCount = 0;
	}
	
	static {
		loadLibrary(Yices.class);
	}

	/**
	 * Returns a pointer to an instance of Yices.
	 * @return a pointer to an instance of Yices.
	 */
	private static native long make();
	private static native long allocArray();
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#free(int)
	 */
	void free(long peer){
		if(array!=0){		
			free(peer,array);
		//System.out.println("free");
			array = 0;
		}
	}
	
	protected native void free(long peer, long array);
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#addVariables(int, int)
	 */
	void addVariables(long peer, int numVariables){
		//System.out.println(peer);
		natAddVariables(peer,array,numVariables,(super.numberOfVariables()) - numVariables);
	}

	native long natAddVariables(long peer,long array,int numVariables, int currentVarCount);
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#addClause(int, int[])
	 */
	boolean addClause(long peer, int[] lits){
		boolean res = natAddClause(peer,lits,makearray, array);
		makearray = false;
		return res;
	}
	
	native boolean natAddClause(long peer,int[] lits,boolean makearray, long array);

	@Override
	public int numberOfTargets() {
		return targetCount;
	}

	@Override
	public boolean addTarget(int lit) {
		// TODO Auto-generated method stub
		targetCount++;
		return addTarget(super.peer(),lit,array);
	}
	
	native boolean addTarget(long peer ,int lit,long array);

	@Override
	public boolean clearTargets() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addWeight(int lit, int weight) {
		// TODO Auto-generated method stub
		return addWeight(super.peer(),lit,weight,array);
	}
	
	native boolean addWeight(long peer,int lit, int weight,long array);
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.NativeSolver#valueOf(int, int)
	 */
	native boolean valueOf(long peer, int literal);
	private int targetCount;
	
	@Override
	native boolean solve(long peer);

	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "PMaxYicesNative";
	}

}
	
