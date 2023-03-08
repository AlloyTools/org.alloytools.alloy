package ca.uwaterloo.watform.parser;

// tmp
import java.util.*;

import java.io.FileReader;
import java.io.BufferedReader;

import java.io.FileNotFoundException;

import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;


import edu.mit.csail.sdg.parser.CompModule;

import ca.uwaterloo.watform.core.DashSituation;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.ast.*;

import ca.uwaterloo.watform.parser.CompModuleHelper;

public class DashModule extends CompModuleHelper {

	// besides creating a DashState; parsing also has count buffers and create indexes
	// for those buffers in order to have the correct open statements

	private DashState root = null;
	public String filename = null;
	public Integer rootStartLine = null;
	public Integer rootEndLine = null;
	private int numBuffers = 0;
	private SymbolTable symbolTable;

	// can't ever be initialized with another world
	public DashModule(String filename) {
		super(null,filename,null);
		assert (!DashOptions.isElectrum && (DashOptions.isTcmc || DashOptions.isTraces));
		// do the open stmts for Dash after we know how many buffers
		if (DashSituation.haveCountedBuffers) {
			importModules(DashSituation.bufferElements);
			// because DashModule is created again for every recursive call
			// make sure we only do this once on second parsing pass
			DashSituation.haveCountedBuffers = false;
		}

	}
	public DashModule(CompModule world, String filename, String path) {
		// super must be first statement in constructor
		super(world,filename,path);
		// this function is just for compatibility with copied CompUtil -> DashUtil
		assert(world == null && path == null);
		// do the open stmts for Dash after we know how many buffers
		if (DashSituation.haveCountedBuffers) {
			importModules(DashSituation.bufferElements);
			// because DashModule is created again for every recursive call
			// make sure we only do this once on second parsing pass
			DashSituation.haveCountedBuffers = false;
		}
	}
	public int nextBufferIndex() {
		numBuffers++;
		return numBuffers - 1;
	}
	public int getNumBuffers() {
		return numBuffers;
	}
	public void setRoot(DashState r) {
		assert(r != null);
		root = r;

	}
	
	public String toString() {
		String s = "";

		try {
			if (root != null) {
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
		    	for (int i = 0; i < rootStartLine-1; i++) {
		    		s += br.readLine() + "\n";
		    	}
				
				// eventually print everything
				if (root != null) {
					s += root.toString();
				}
				// skip stuff
				for (int i = 0; i <= rootEndLine - rootStartLine+1; i++) {
					br.readLine();
				}
				// add the rest of the lines
				String k;
				while ((k = br.readLine()) != null) {
					s += k + "\n";
				}
			} else {
				// just put all the lines in the string
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
				String k;
				while ((k = br.readLine()) != null) {
					s += k + "\n";
				}
			}
		} catch (Exception FileNotFoundException) {
			// we know the file exists so this exception should never be thrown
			// Fix this
			System.err.println("File Not Found");
		}
		/*
		if (rootStartLine != null) {
			s += "Path " + getFilePath()  +"\n";
			s += "Dash file start line " + rootStartLine + "\n";
			s += "Dash end line " + rootEndLine +"\n";
		}
		*/
		// how to print the Alloy stuff we add?
		// s += sigsToString();
		return s;
	}
	// helper functions for creating parts of module 
	/*
    public static createDecl(ExprVar v, Expr e) {
        return new Decl(null, null, null, null, v, mult(e));
    }
    public static createOneDecl(String v, String typ) {
        return createDecl(createVar(v), createOne(createVar(typ));
    }
    public static createSetDecl(String v, String typ) {
        return createDecl(createVar(v), createSet(createVar(typ));
    }
	*/


	public void importModules(List<String> bufElements) {
        String noAlias = null;
        this.addOpenSimple(DashStrings.utilBooleanName, null, noAlias); 
        if (DashOptions.isTcmc) {
            this.addOpenSimple(DashStrings.utilCTLpathName, Arrays.asList(DashStrings.snapshotName), noAlias);
        }
        else if (DashOptions.isTraces)  {
            this.addOpenSimple(DashStrings.utilOrderingName, Arrays.asList(DashStrings.snapshotName),DashStrings.snapshotName);
        }
        // add the open statements for the buffers
        // if (bufElements != null )     
        //for (String name: bufElements) {
            // perhaps this can be simplified
            //this.addOpen(DashStrings.utilBufferName, Arrays.asList("fix this", "fixthis"), "fix this");
        //}
    }
	/*
	private List<String> params;
	private StateTable stateTable;
	private TransTable transTable;
	private SymbolTable symbolTable;
	private EventTable eventTable;
	public boolean hasConcurrency;


	private int bufferMax;
	// everything else is stored in the root State

	public void DashModule(DashState r) {
		this.root = r;
		// 0 is the first buffer number
		this.bufferMax = -1 ;
	}

	public String getRoot() {
		return root.name(); // as root it is already FQN
	}
	public boolean hasInternalEvents() {
		return (eventTable.hasInternalEvents());
	}
	public boolean hasEnvironmentalEvents() {
		return (eventTable.hasExternalEvents());
	}
	public boolean hasEvents() {
		return (hasInternalEvents() || hasEnvironmentalEvents())
	}
	public List<String> getAllInternalEventNames() {
		assert(r.hasAllInternalEvents());
		return eventTable.getInternalEvent();
	}
	public List<String> getAllEnvironmentalEventNames() {
		assert(r.hasAllExternalEvents());
		return eventTable.getEnvironmentalEvents();
	}
	public List<String> getTransitionNames() {
		return transTable.getNames();
	}
	public List<String> getTransTriggerEvents(String t){
		return transTable.get(t).trigger();
	}
	public List<String> getTransGenEvents(String t) {
		return transTable.get(t).genEvents();
	}
	public List<String> getEventParams(String e) {
		return eventTable.get(e).getParams();
	}
	public List<String> getAllParams() {
		return params;
	}
	public int getNumParams() {
		return params.size();
	}
	public List<String> getBufferIndices() {
		List<String> iList;
		for (i = 0; i <= r.getBufferMax(); i++) {
			iList.add(DashStrings.bufferIndexName + i)
		return iList;
	}
	public boolean hasConcurrency() {
		///???? at least one concurrent state
	}

	public List<DashDynVars> getDynSymbols() {
		return symbolTable.values();
	}
	public List<DashDynVars> getBuffers() {

	}
	public List<DashExpr> getInvariants() {
		/????
	}
	public List<String> getTransitionsAtLevel(int i) {
		ArrayList<String> o = transTable.keys().stream().filter(t -> transTable.get(t).params.size() == i).collect(Collectors.toList());
		return o;		
	}
	public List<String> getTransParams(String t) {
		return transTable.get(t).getParams();
	}
	public ArrayList<String> getBasicStatesEnteredAtLevel(i){
		ArrayList<String> bs = stateTable.get(root).basicStatesEntered;
		ArrayList<String> o = bs.stream().filter(s -> s.params.size() == i).collect(Collectors.toList());
		return o;
	}
	public List<String> createStateArrow(String s) {
		return createArrow(stateTable.get(s).params.add(s));
	}


	public boolean hasBuffers() {
		return (bufferMax != -1);
	}
	public int getBufferMax() {
		return bufferMax;
	}

	public void resolveAll() {
		root.resolveAll();
		// if root has no substates?
		// if no transitions?
		stateTable.resolveAll();
		transTable.resolveAll();
	}

	public boolean isBasic(String s) {
		return (stateTable.get(s).immediateChildren == null);
	}
	*/
}