package ca.uwaterloo.watform.parser;

// tmp
import java.util.*;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CompModule;


import ca.uwaterloo.watform.core.*;
import ca.uwaterloo.watform.ast.*;

import ca.uwaterloo.watform.parser.CompModuleHelper;
import ca.uwaterloo.watform.dashtoalloy.DashToAlloy;

public class DashModule extends CompModuleHelper {

	private DashState root = null;

	// after parsing, these allow us to echo the Alloy-only parts
	// of the file when printing
	public String filename = null;
	public Integer rootStartLine = null;
	public Integer rootEndLine = null;

	// derived during resolveAllDash phase
	private int numBuffers = 0;
	private SymbolTable symbolTable;
	private StateTable stateTable = new StateTable();
	private TransTable transTable = new TransTable();

	// once created and parsed, the following are
	// the phases of a DashModule
	// all operations happen in place
	// to the final DashModule also contains the original
	// parsed Dash
	public static enum Status {
		CREATED,
		PARSED,
		RESOLVED_DASH,
		TRANSLATED_TO_ALLOY,
		RESOLVED_ALLOY,
		ERROR
	}
	private Status status = Status.CREATED;

	// strings for statements resulting from the translation
	public String alloyString = new String();
	// the open statements added for Dash translation to Alloy 
	// go at the beginning of the model so these are separate from the others
	private String opens = new String();
	// the statement for opening util/boolean is separate
	// b/c we don't want to repeat it if the user has 
	// included it in the model
	private String booleanOpen = new String();

	// can't ever be initialized with another world
	public DashModule(String filename) {
		super(null,filename,null);
		initializeDashModule();
	}
	public DashModule(CompModule world, String filename, String path) {
		// this function is just for compatibility with copied CompUtil -> DashUtil
		// super must be first statement in constructor
		super(world,filename,path);
		assert(world == null && path == null);
		initializeDashModule();
	}
	private void initializeDashModule() {	
		assert (!DashOptions.isElectrum && (DashOptions.isTcmc || DashOptions.isTraces));
		// do the open stmts for Dash after we know how many buffers
		// b/c the opens are parsed during parsing
		if (DashSituation.haveCountedBuffers) {
			importModules(DashSituation.bufferElements, DashSituation.bufferNames);
			// because a DashModule is created for every parse of a file
			// including recursively for open stmts
			// make sure we only do import on second parsing pass
			DashSituation.haveCountedBuffers = false;
		}		
	}

	// printing -----------------------------------------------------
	public String toString() {
		if (status == Status.RESOLVED_ALLOY) return toStringAlloy();
		else return toStringRegular();
	}
	public String toStringRegular() {
		String s = "";
		try {
			if (root != null) {
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
				String r;
				for (int j= 0; j < rootStartLine-1; j++) {
					r = br.readLine();
					s += r +"\n";
				}
				if (root != null) s += root.toString();
				// skip Dash stuff
				for (int i = 0; i <= rootEndLine - rootStartLine+1; i++) br.readLine();
				// add the rest of the lines
				String rr;
				while ((rr = br.readLine()) != null) s += rr + "\n";
			} else {
				// just put all the lines in the string because there is no Dash part
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
				String k;
				while ((k = br.readLine()) != null) s += k + "\n";
			}
		} catch (Exception FileNotFoundException) {
			// we know the file exists so this exception should never be thrown
			System.err.println("File Not Found");
		}
		return s;
	}
	public String toStringAlloy() {	
		String s = "";
		/*
		if (rootStartLine != null) {
			s += "Path " + getFilePath()  +"\n";
			s += "Dash file start line " + rootStartLine + "\n";
			s += "Dash end line " + rootEndLine +"\n";
		}
		*/
		
		try {
			if (root != null) {
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
				// put the extra open statements at the beginning or right after 'module'
				String r;
				Integer k = 0;
				Boolean writeBooleanOpen = true;
				if (rootStartLine == 1) s += opens;
				else {	
					for (int j= 0; j < rootStartLine-1; j++) {
						k = j;
						r = br.readLine();
						if (!(r.replaceAll("\\s+","").equals(""))) {
							if (r.contains(DashStrings.moduleName) || r.contains(DashStrings.openName)) {
								if (r.contains(DashStrings.openName) && r.contains(DashStrings.utilBooleanName)) writeBooleanOpen = false;
								s += r +"\n";
							} else {
								if (writeBooleanOpen) s += booleanOpen;
								s += opens + "\n";
								// have to write the line after module/opens
								s += r +"\n";
								break;
							}
						} else s += "\n";
					}
					// there was nothing before "state"
					if (k == rootStartLine-1) s += opens;
					if (k+1 < rootStartLine-1) {
			    		for (int i = k+1; i < rootStartLine -1 ; i++) s += br.readLine() + "\n";
			    	}
			    }
				
				// skip Dash stuff
				for (int i = 0; i <= rootEndLine - rootStartLine+1; i++) br.readLine();
				// add the rest of the lines
				String rr;
				while ((rr = br.readLine()) != null) s += rr + "\n";
				s += alloyString;
			} else {
				// just put all the lines in the string because there is no Dash part
				BufferedReader br = new BufferedReader(new FileReader(getFilePath()));
				String k;
				while ((k = br.readLine()) != null) s += k + "\n";
			}
		} catch (Exception FileNotFoundException) {
			// we know the file exists so this exception should never be thrown
			System.err.println("File Not Found");
		}
		return s;
	}

	// needed during parsing -------------------------

	public void importModules(List<String> bufElements, List<String> bufNames) {
		System.out.println("Adding open stmts");
        String noAlias = null;
        booleanOpen = this.addOpenSimple(DashStrings.utilBooleanName, null, noAlias); 
        if (DashOptions.isTcmc) 
        	opens += this.addOpenSimple(DashStrings.utilCTLpathName, Arrays.asList(DashStrings.snapshotName), noAlias);
        else if (DashOptions.isTraces) 
        	opens += this.addOpenSimple(DashStrings.utilOrderingName, Arrays.asList(DashStrings.snapshotName),DashStrings.snapshotName);
        // add the open statements for the buffers
        if (bufElements != null ) 
        	for (int i = 0; i < bufElements.size(); i++) 
            	opens += this.addOpenSimple(DashStrings.utilBufferName, Arrays.asList(DashStrings.bufferIndexName+i, bufElements.get(i)), bufNames.get(i));
    }

    // constructors/accessor functions ------------------

	public void setRoot(DashState r) {
		assert(r == null);
		root = r;
	}
	public boolean hasRoot() {
		return (root != null);
	}
	public String getRootName()  {
		if (root != null) return root.name;
		else { DashErrors.toAlloyNoDash(); return null; }
	}
	public int getNumBuffers() {
		return numBuffers;
	}

	public boolean isBasicState(String s) {
		return (stateTable.isBasicState(s));
	}

    public List<String> getImmChildren(String parent) {
    	return stateTable.getImmChildren(parent);
    }
    public Set<String> getTransNames() {
    	return transTable.getTransNames();
    }
    public boolean hasInternalEvents() {
		return false; // (eventTable.hasInternalEvents());
	}
	public boolean hasEnvironmentalEvents() {
		return false; //(eventTable.hasExternalEvents());
	}
	public boolean hasEvents() {
		return false; //(hasInternalEvents() || hasEnvironmentalEvents())
	}
	public boolean hasConcurrency() {
		return stateTable.hasConcurrency(root.name);
	}
	public int getMaxDepthParams() {
		// could precalculate this
		return stateTable.getMaxDepthParams();
	}
	public List<String> getTransParams(String t) {
		return transTable.getParams(t);
	}
	public List<String> getAllParams() {
		return stateTable.getAllParams();
	}
	// processes  ---------------------------------------

	public void resolveAllDash(A4Reporter rep) {
		assert(status == Status.PARSED);
		System.out.println("Resolving Dash");
		if (root != null ) {
			// passed with empty set of params, empty set of ancestors
			stateTable.setRoot(root.name);
			root.resolveAllStates(stateTable,new ArrayList<String>(),new ArrayList<String>());
			// have to do states first so siblings of trans parent state
			// are in place to search for src/dest
			root.resolveAllTrans(stateTable,transTable);
			System.out.println(stateTable.toString());
			System.out.println(transTable.toString());
			// if root has no substates?
			// if no transitions?
			stateTable.resolveAll(getRootName());
			transTable.resolveAll();
		}
		status = Status.RESOLVED_DASH;
	}

	public void translate() {
		assert(status == Status.RESOLVED_DASH);
		System.out.println("Translating to Alloy");
		// this is so we can partition the translation
		// code into a different file
		DashToAlloy d = new DashToAlloy(this);
		// translation is done in place
		d.translate();
		// if no errors 
		status = Status.TRANSLATED_TO_ALLOY;
	}
	public void resolveAllAlloy(A4Reporter rep) {
    	// this method in CompModule is static and takes a CompModule as
    	// input and returns one as output even though it makes all the 
    	// changes in place on the input CompModule and then just
    	// returns it as the output
    	// so here we cast DashModule to CompModule and ignore the
    	// output CompModule
    	assert(status == Status.TRANSLATED_TO_ALLOY);
    	System.out.println("Resolving Alloy");
    	// this quits if it throws an error
    	//resolveAll(rep == null ? A4Reporter.NOP : rep, this);
    	// if no errors
    	status = Status.RESOLVED_ALLOY;
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



	/*
	private List<String> params;
	private StateTable stateTable;
	private TransTable transTable;
	private SymbolTable symbolTable;
	private EventTable eventTable;
	public boolean hasConcurrency;



	public String getRoot() {
		return root.name(); // as root it is already FQN
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

	public int getNumParams() {
		return params.size();
	}
	public List<String> getBufferIndices() {
		List<String> iList;
		for (i = 0; i <= r.getBufferMax(); i++) {
			iList.add(DashStrings.bufferIndexName + i)
		return iList;
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




	*/
}