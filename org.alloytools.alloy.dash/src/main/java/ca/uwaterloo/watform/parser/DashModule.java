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
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.*;
import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import ca.uwaterloo.watform.ast.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.parser.CompModuleHelper;
import ca.uwaterloo.watform.dashtoalloy.DashToAlloy;

public class DashModule extends CompModuleHelper {

	// let it be a list so we can have a good error message in wff checks (resolveAllDash)
	private List<DashState> roots = new ArrayList<DashState>();
	private DashState root = null; // normally first element of roots

	// after parsing, these allow us to echo the Alloy-only parts
	// of the file when printing
	public String filename = null;
	public Integer rootStartLine = null;
	public Integer rootEndLine = null;

	// derived during resolveAllDash phase
	private int numBuffers = 0;
	private int maxDepthParams = 0;
	private boolean[] transAtThisParamDepth; 
	private SymbolTable symbolTable;
	private StateTable stateTable = new StateTable();
	private TransTable transTable = new TransTable();
	private EventTable eventTable = new EventTable();
	private VarTable varTable = new VarTable();
	private BufferTable bufferTable = new BufferTable();

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
		// this is violated so something in Alloy parsing must call this within a world
		// assert(world == null && path == null);
		// as long as super is doing copying from incoming world to current world
		// this should be fine
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
		//System.out.println("Adding open stmts");
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

    // constructors 

	public void addRoot(DashState r) {
		roots.add(r);
	}
	public void setParsed() {
		assert(status == Status.CREATED);
		status = Status.PARSED;
	}

	// general query
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
		return maxDepthParams;
	}
	public List<String> getAllParams() {
		return stateTable.getAllParams();
	}

	//stuff about states (some of these are to expose the stateTable for testing)
	public boolean isLeaf(String s) {
		return (stateTable.isLeaf(s));
	}
	public boolean isAnd(String s) {
		return stateTable.isAnd(s);
	}
	public boolean isRoot(String s) {
		return stateTable.isRoot(s);
	}
    public List<String> getImmChildren(String parent) {
    	return stateTable.getImmChildren(parent);
    }
    public List<DashRef> getLeafStatesExited(DashRef s) {
    	return stateTable.getLeafStatesExited(s);
    }
    public List<DashRef> getLeafStatesEntered(DashRef s) {
    	return stateTable.getLeafStatesEntered(s);
    }
    public List<DashRef> getLeafStatesEnteredWithScope(DashRef context, DashRef s) {
    	return null; //stateTable.getLeafStatesEnteredWithScope(context, s);
    }
    public List<String> getAllAnces(String sfqn) {
    	return stateTable.getAllAnces(sfqn);
    }
    public String getClosestConcAnces(String sfqn) {
		return stateTable.getClosestConcAnces(sfqn);
	}
	public List<String> getAllNonConcDesc(String sfqn) {
		return stateTable.getAllNonConcDesc(sfqn);
	}
	public List<String> getRegion(String sfqn) {
		return stateTable.getRegion(sfqn);
	}

    // stuff about transitions
    public Set<String> getTransNames() {
    	return transTable.getTransNames();
    }
    public DashRef getTransSrc(String tfqn) {
    	return transTable.getSrc(tfqn);
    }
    public DashRef getTransDest(String tfqn) {
    	return transTable.getDest(tfqn);
    }
    public List<String> getHigherPriTrans(String tfqn) {
    	return transTable.getHigherPriTrans(tfqn);
    }

	public Boolean transAtThisParamDepth(int i) {
		if (i > maxDepthParams) { DashErrors.tooHighParamDepth(); return null; }
		else
			return transAtThisParamDepth[i];
	}
	public List<String> getTransParams(String t) {
		return transTable.getParams(t);
	}

	// stuff about both states and trans
	public DashRef getScope(String tfqn) {
		DashRef src = getTransSrc(tfqn);
		DashRef dest = getTransDest(tfqn);
		String sc = DashFQN.longestCommonFQN(src.getName(),dest.getName());
		// maxCommonParams is max number of params that could have in common
		// but they don't necessarily have the same values
		Integer maxCommonParams = stateTable.getParams(sc).size();
		List<Expr> scopeParams = new ArrayList<Expr>();
		Expr equals = null;
		Expr s = null;
		Expr d = null;
		for (int i=0;i<maxCommonParams;i++) {
			s = src.getParamValues().get(i);
			d = dest.getParamValues().get(i);
			if (sEquals(s,d)) {
				// syntactically equal
				scopeParams.add(s);
			} else {
				equals = createEquals(s,d);
				scopeParams.add(
					createITE(
						equals,
						s,
						createVar(stateTable.getParams(sc).get(i))));  // whole set
				for (int j=i+1;j<maxCommonParams;j++) {
					s = src.getParamValues().get(j);
					d = dest.getParamValues().get(j);
					if (sEquals(s,d)) {
						// syntactically equal
						scopeParams.add(s);
					} else {
						equals = createAnd(equals,createEquals(s,d));
						scopeParams.add(
							createITE(
								equals,
								s,
								createVar(stateTable.getParams(sc).get(j))));  // whole set
					}
				}
				break;
			}
		}
		return new DashRef (sc,scopeParams);
	}
	// returns the list of states with params
	// that are exited when taking trans t
	public List<DashRef> exited(String tfqn) {
		DashRef scope = getScope(tfqn);
		return stateTable.getLeafStatesExited(scope);
	}
	// for debugging
	public List<DashRef> allPrefixDashRefs(DashRef x) {
		return stateTable.allPrefixDashRefs(x);
	}
	public List<DashRef> entered(String tfqn) {
		return stateTable.getLeafStatesEnteredInScope(
				getScope(tfqn),
				getTransDest(tfqn));
	}

	public List<DashRef> onlyConc(List<DashRef> dr) {
		return dr.stream()
			.filter(x -> isAnd(x.getName()))
			.collect(Collectors.toList());
	}
	public List<DashRef> scopesUsed(String tfqn) {
		DashRef scope = getScope(tfqn);
		List<DashRef> aP = allPrefixDashRefs(scope);
		List<DashRef> aPc = onlyConc(aP);
		List<DashRef> r = new ArrayList<DashRef>();
		List<Expr> prms;
		Expr e;
		Expr p;
		if (aPc.isEmpty()) {
			// no concurrent states in scope prefix
			// so just add root
			r.add(aP.get(0));
		} else {
			for (DashRef s: allButLast(aPc)) {
				// if a prefix scope includes all param values, it really
				// is the scope
				if (isAnd(s.getName()) && stateTable.hasParam(s.getName())) {
					prms = new ArrayList<Expr>(allButLast(s.getParamValues()));
					e = lastElement(s.getParamValues());
					p = createITE(createEquals(e,createVar(stateTable.getParam(s.getName()))),
							  createVar(stateTable.getParam(s.getName())),
							  createNone());
					prms.add(p);
					r.add(new DashRef(s.getName(), prms));
				}
			}
			// if it has a parameter it will be included
			r.add(lastElement(aPc));
		}
		return r;
	}
	public List<DashRef> nonOrthogonalScopesOf(String tfqn) {
		DashRef scope = getScope(tfqn);
		//System.out.println(allPrefixDashRefs(scope));
		List<DashRef> aP = allPrefixDashRefs(scope);
		// always needs to include Root
		List<DashRef> r = new ArrayList<DashRef>();
		r.add(aP.get(0));
		r.addAll(onlyConc(aP));
		return r;
	}
	// processes  ---------------------------------------

	public void debug() {
		System.out.println(stateTable.toString());
		System.out.println(transTable.toString());
		System.out.println(eventTable.toString());		
		System.out.println(varTable.toString());
	}
	public void debug(String tfqn) {
		System.out.println(stateTable.toString());
		System.out.println(transTable.toString());
		System.out.println(eventTable.toString());
		System.out.println(varTable.toString());
		for (String x: getTransNames()) {
			// System.out.println(tfqn +" scope :" + getScope(x));
		}
		if (tfqn != null) {
			System.out.println("src " + getTransSrc(tfqn));
			System.out.println("dest " + getTransDest(tfqn));
			System.out.println("getScope " + getScope(tfqn));
			System.out.println("getClosestConcAnces: "+getClosestConcAnces(getTransSrc(tfqn).getName()));
			System.out.println("getAllNonConcDesc: " +getAllNonConcDesc(getClosestConcAnces(getTransSrc(tfqn).getName())));
			System.out.println("getRegion:"+"Root/S1/S2: "+getRegion(getTransSrc(tfqn).getName()));
			System.out.println("exited: " + exited(tfqn));		
			System.out.println("entered" + getLeafStatesEntered(getTransDest(tfqn)));
			System.out.println("enteredInScope" + entered(tfqn));
			System.out.println("allPrefixDashRefs of scope: "+ allPrefixDashRefs(getScope(tfqn)));
			System.out.println("scopesUsed: "+ scopesUsed(tfqn));
			System.out.println("nonOrthogonalScopes: " + nonOrthogonalScopesOf(tfqn));
		}
	}
	// should we use the rep arg here?
	public void resolveAllDash(A4Reporter rep) {

		//System.out.println("Resolving Dash");
		if (roots.isEmpty()) {
			DashErrors.noStates();
		} else if (roots.size() > 1) {
			DashErrors.onlyOneState(roots.get(1).getPos());
		} else {
			root = roots.get(0);
			// passed with empty set of params, empty set of ancestors
			stateTable.setRoot(root.name);
			root.resolveAllStates(stateTable,eventTable, varTable, bufferTable, new ArrayList<String>(),new ArrayList<String>());
			// have to do states first so siblings of trans parent state
			// are in place to search for src/dest
			root.resolveAllTrans(stateTable,transTable);
			// if root has no substates?
			// if no transitions?
			stateTable.resolveAll(getRootName());
			// TODO will need eventTable
			transTable.resolveAll();
			maxDepthParams = stateTable.getMaxDepthParams();
			  //transAtThisParamDepth = new boolean[maxDepthParams+1];
			transAtThisParamDepth = transTable.transAtThisParamDepth(maxDepthParams);
			//
			//debug("Root/S1/t1");
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
    	//assert(status == Status.TRANSLATED_TO_ALLOY);
    	//System.out.println("Resolving Alloy");
    	// this quits if it throws an error
    	//resolveAll(rep == null ? A4Reporter.NOP : rep, this);
    	// if no errors
    	status = Status.RESOLVED_ALLOY;
    }

    // for testing
    public List<String> getDefaults(String s) {
    	return stateTable.getDefaults(s);
    }



    /* leftover
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