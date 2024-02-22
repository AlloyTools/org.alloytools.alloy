package ca.uwaterloo.watform.parser;


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
import java.time.format.DateTimeFormatter;  
import java.time.LocalDateTime;    





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
import ca.uwaterloo.watform.dashtoalloy.Common;

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
	private int maxDepthParams = 0;
	private boolean[] transAtThisParamDepth; 
	//private SymbolTable symbolTable;
	private StateTable stateTable = new StateTable();
	private TransTable transTable = new TransTable();
	private EventTable eventTable = new EventTable();
	private VarTable varTable = new VarTable();
	private PredTable predTable = new PredTable();


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

	
   	DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");  
   	LocalDateTime now = LocalDateTime.now();  

    // strings for statements resulting from the translation
	public String alloyString = new String();
	public String commentString = new String(
		"/*\n" +
		"   Automatically created via translation of a Dash model to Alloy\n" +
		"   on "+dtf.format(now) + "\n" +
		"*/\n\n"
		);
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
		//assert (!DashOptions.isElectrum && (DashOptions.isTcmc || DashOptions.isTraces));
		// do the open stmts for Dash after we know how many buffers
		// b/c the opens are parsed during parsing
		if (DashSituation.haveCountedBuffers) {
			importModules(DashSituation.bufferElements, DashSituation.bufferNames);
			// because a DashModule is created for every parse of a file
			// including recursively for open stmts
			// make sure we only do import on second parsing pass
			DashSituation.haveCountedBuffers = false;
			DashSituation.bufferIndex = 0;
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
		String s = new String(commentString);
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
				Boolean wroteOpens = false;
				//System.out.println(opens);
				//if (rootStartLine == 1) {
					// assume there were no opens in the file
				//	s += booleanOpen;
				//	s += opens;
				//} else {	

				//System.out.println(rootStartLine);

				// lines in file start counting at 1
				k = 0;
					for (int j= 0; j < rootStartLine-1; j++) {
						k = j;
						//System.out.println(j);
						r = br.readLine();
						// empty line
						if (!(r.replaceAll("\\s+","").equals(""))) {
							if (r.contains(DashStrings.moduleName) || r.contains(DashStrings.openName)) {
								//make sure we don't open boolean twice
								if (r.contains(DashStrings.openName) && r.contains(DashStrings.utilBooleanName)) writeBooleanOpen = false;
								s += r +"\n";
							} else {
								// we've reached the end of the opens in the file
								// now add our own opens and quit this loop
								if (writeBooleanOpen) s += booleanOpen;
								s += opens + "\n";
								// have to write the line after module/opens
								// that we just read
								s += r +"\n";
								wroteOpens = true;
								break;
							}
						} else s += "\n";
					}
					if (!wroteOpens) { s += booleanOpen; s += opens; }
					// add all the lines after the opens and before 'state'
					if (k+1 < rootStartLine-1) {
			    		for (int i = k+1; i < rootStartLine -1 ; i++) s += br.readLine() + "\n";
			    	}
			    //}
				
				// skip Dash stuff
				for (int i = 0; i <= rootEndLine - rootStartLine+1; i++) br.readLine();
				// print the translated Dash
				s += alloyString;
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

	// needed during parsing -------------------------

	public void importModules(List<String> bufElements, List<String> bufNames) {
		//System.out.println("Adding open stmts");
        String noAlias = null;
        // module might already include it
        // safe to reopen it internally?
        // but don't want it printed twice?
        booleanOpen = this.addOpenSimple(DashStrings.utilBooleanName, null, noAlias); 
        if (DashOptions.isTcmc) 
        	opens += this.addOpenSimple(DashStrings.utilTcmcPathName, Arrays.asList(DashStrings.snapshotName), noAlias);
        else if (DashOptions.isTraces) 
        	opens += this.addOpenSimple(DashStrings.utilTracesName, Arrays.asList(DashStrings.snapshotName),DashStrings.snapshotName);
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
	public boolean hasOnlyOneState() {
		return stateTable.hasOnlyOneState();
	}
	public String getRootName()  {
		if (root != null) return root.name;
		else { DashErrors.toAlloyNoDash(); return null; }
	}
	public List<Integer> getBufferIndices() {
		return varTable.getBufferIndices();
	}
	public boolean hasBuffers() {
		return (!getBufferIndices().isEmpty());
	}
    public boolean hasInternalEvents() {
		return eventTable.hasInternalEvents();
	}
	public boolean hasEnvironmentalEvents() {
		return eventTable.hasEnvironmentalEvents();
	}
	public boolean hasEvents() {
		return eventTable.hasEvents();
	}
	public boolean hasEventsAti(int i) {
		return eventTable.hasEventsAti(i);
	}
	public boolean hasInternalEventsAti(int i) {
		return eventTable.hasInternalEventsAti(i);
	}
	public boolean hasEnvironmentalEventsAti(int i) {
		return eventTable.hasEnvironmentalEventsAti(i);
	}
	public boolean hasConcurrency() {
		return stateTable.hasConcurrency(root.name);
	}
	public int getMaxDepthParams() {
		// could precalculate this
		return maxDepthParams;
	}
	public List<String> getAllParamsInOrder() {
		return stateTable.getAllParamsInOrder();
	}

	public List<String> getAllStateNames() {
		return stateTable.getAllStateNames();
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
    public String getClosestParamAnces(String sfqn) {
		return stateTable.getClosestParamAnces(sfqn);
	}
	public List<String> getAllNonParamDesc(String sfqn) {
		return stateTable.getAllNonParamDesc(sfqn);
	}
	public List<String> getRegion(String sfqn) {
		return stateTable.getRegion(sfqn);
	}
	public List<Integer> getTransParamsIdx(String tfqn) {
		return transTable.getParamsIdx(tfqn);
	}
    // stuff about transitions
    public List<String> getAllTransNames() {
    	return transTable.getAllTransNames();
    }

    public DashRef getTransSrc(String tfqn) {
    	return transTable.getSrc(tfqn);
    }
    public DashRef getTransDest(String tfqn) {
    	return transTable.getDest(tfqn);
    }
    public DashRef getTransOn(String tfqn) {
    	return transTable.getOn(tfqn);
    }
    public Expr getTransDo(String tfqn) {
    	return transTable.getDo(tfqn);
    }
    public Expr getTransWhen(String tfqn) {
    	return transTable.getWhen(tfqn);
    }
    public DashRef getTransSend(String tfqn) {
    	return transTable.getSend(tfqn);
    }
    public List<String> getHigherPriTrans(String tfqn) {
    	return transTable.getHigherPriTrans(tfqn);
    }

    public boolean isEnvironmentalEvent(String efqn) {
    	return eventTable.isEnvironmentalEvent(efqn);
    }
    public boolean isInternalEvent(String efqn) {
    	return eventTable.isInternalEvent(efqn);
    }
    public boolean hasVar(String name) {
    	return varTable.hasVar(name);
    }
    public List<String> getAllVarNames() {
    	return varTable.getAllVarNames();
    }
    public List<String> getAllInternalVarNames() {
    	return varTable.getAllVarNames().stream()
    			.filter(i -> varTable.isInternal(i))
    			.collect(Collectors.toList());
    }
    public List<String> getVarBufferParams(String vfqn) {
    	return varTable.getParams(vfqn);
    }
    public List<Integer> getVarBufferParamsIdx(String vfqn) {
    	return varTable.getParamsIdx(vfqn);
    }
    public Expr getVarType(String vfqn) {
    	return varTable.getVarType(vfqn);
    }
	public Boolean transAtThisParamDepth(int i) {
		if (i > maxDepthParams) { DashErrors.tooHighParamDepth(); return null; }
		else
			return transAtThisParamDepth[i];
	}
	public List<String> getTransParams(String t) {
		return transTable.getParams(t);
	}

	public List<Expr> getInits() {
		return stateTable.getInits();
	}
	public List<Expr> getInvs() {
		return stateTable.getInvs();
	}
	public List<String> getAllBufferNames() {
		return varTable.getAllBufferNames();
	}
	public int getBufferIndex(String bfqn) {
		return varTable.getBufferIndex(bfqn);
	}
	public String getBufferElement(String bfqn) {
		return varTable.getBufferElement(bfqn);
	}
	public boolean isInternal(String vfqn) {
		// works for buffers also
		return varTable.isInternal(vfqn);
	}
	// stuff about both states and trans
	public DashRef getScope(String tfqn) {
		// this is not necessarily an AND scope
		DashRef src = getTransSrc(tfqn);
		DashRef dest = getTransDest(tfqn);
		String sc = DashFQN.longestCommonFQN(src.getName(),dest.getName());
		// maxCommonParams is max number of params that could have in common
		// but they don't necessarily have the same values
		Integer maxCommonParams = stateTable.getParamsIdx(sc).size();
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
		return DashRef.createStateDashRef (sc,scopeParams);
	}
	public DashRef getConcScope(String tfqn) {
		DashRef scope = getScope(tfqn);
		List<DashRef> aP = allPrefixDashRefs(scope);
		List<DashRef> aPc = onlyConcPlusRoot(aP);
		return lastElement(aPc); // might be the scope
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
	public List<DashRef> initialEntered() {
		return stateTable.getRootLeafStatesEntered();
	}
	public List<DashRef> onlyConcPlusRoot(List<DashRef> dr) {
		List <DashRef> c = emptyList();
		c.add(DashRef.createStateDashRef(stateTable.getRoot(),emptyList()));
		c.addAll(dr.stream()
			.filter(x -> isAnd(x.getName()))
			.collect(Collectors.toList()));
		return c;
	}
	public List<DashRef> ancesConcScopes(DashRef d) {
		// includes d if it is a conc state
		List<DashRef> aP = allPrefixDashRefs(d);
		List<DashRef> aPc = onlyConcPlusRoot(aP);
		return aPc;		
	}
	public List<DashRef> scopesUsed(String tfqn) {
		// includes Root only if that is the only scope
		List<DashRef> aPc = ancesConcScopes(getScope(tfqn));
		List<DashRef> r = new ArrayList<DashRef>();

		// System.out.println(aPc);
		if (aPc.size() == 1) {
			// scope must be the root
			// so add it
			r.add(aPc.get(0));
		} else {
			// don't put the root in unless
			// the root is the scope
			r = DashUtilFcns.tail(aPc);
			
		}
		return r;
		/*
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
				// so we shouldn't need this
				if (isAnd(s.getName()) && stateTable.hasParam(s.getName())) {
					prms = new ArrayList<Expr>(allButLast(s.getParamValues()));
					e = lastElement(s.getParamValues());
					p = createITE(createEquals(e,createVar(stateTable.getParam(s.getName()))),
							  createVar(stateTable.getParam(s.getName())),
							  createNone());
					prms.add(p);
					r.add(DashRef.createStateDashRef(s.getName(), prms));
				}
			}
			// if it has a parameter it will be included
			r.add(lastElement(aPc));
		}
		return r;
		*/
	}
	public List<DashRef> nonOrthogonalScopesOf(String tfqn) {
		List<DashRef> aPc = ancesConcScopes(getConcScope(tfqn));
		// always needs to include Root
		return aPc;
		/*
		List<DashRef> r = new ArrayList<DashRef>();
		r.add(aP.get(0));
		r.addAll(onlyConc(aP));
		return r;
		*/
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
		for (String x: getAllTransNames()) {
			// System.out.println(tfqn +" scope :" + getScope(x));
		}
		if (tfqn != null) {
			System.out.println("src " + getTransSrc(tfqn));
			System.out.println("dest " + getTransDest(tfqn));
			System.out.println("pre " + getTransWhen(tfqn));
			System.out.println("post " + getTransDo(tfqn));
			System.out.println("getScope " + getScope(tfqn));
			System.out.println("getClosestParamAnces: "+getClosestParamAnces(getTransSrc(tfqn).getName()));
			//System.out.println("getAllNonParamDesc: " +getAllNonParamDesc(getClosestConcAnces(getTransSrc(tfqn).getName())));
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
			root.load(stateTable,transTable, eventTable, varTable, predTable, new ArrayList<String>());
			// have to do states first so siblings of trans parent state
			// are in place to search for src/dest
			// root.resolveTransTable(stateTable,transTable);
			// if root has no substates?
			// if no transitions?

			// resolves inits, invariants
			stateTable.resolve(getRootName(), eventTable, varTable, predTable);

			transTable.resolve(stateTable, eventTable, varTable, predTable);
			varTable.resolve(stateTable, eventTable, predTable);


			/*
				2024-02-21 NAD
				Do not allow any overlaps between namespaces: state, trans, event, var, buffers
				because in Electrum items from multiple of these categories can end up in the same
				Alloy namespace such as:
				
				one sig X extends Transitions {}
				var sig X in Typ {}

				If we tried to prefix names with trans_ or state_, FQNs would get VERY long
				Also, we want to be consistent with names across all methods (traces, tcmc, Electrum)
			*/
			
			// varTable and predTable names cannot overlap
			disj(getAllVarNames(),predTable.getAllNames());

			disj(getAllVarNames(),getAllStateNames());
			disj(getAllVarNames(),getAllTransNames());
			disj(getAllVarNames(),getAllEventNames());
			disj(getAllVarNames(),getAllBufferNames());

			disj(getAllTransNames(),getAllStateNames() );
			disj(getAllTransNames(),getAllEventNames() );
			disj(getAllTransNames(),getAllBufferNames() );

			disj(getAllStateNames(), getAllEventNames());
			disj(getAllStateNames(),getAllBufferNames());

			disj(getAllEventNames(), getAllBufferNames());

			maxDepthParams = stateTable.getMaxDepthParams();

			transAtThisParamDepth = transTable.transAtThisParamDepth(maxDepthParams);
			//
			//debug("Root/S1/t1");
		}
		status = Status.RESOLVED_DASH;
	}

	public void disj(List<String> alist, List<String> blist) {
		if (!Collections.disjoint(alist , blist)) {
			List<String> x = alist;
			x.retainAll(blist);
			DashErrors.nameOverlap(x);
		}
	}

	public List<DashRef> primedDashRefs(Expr exp) {
		return varTable.primedDashRefs(exp);
	}

	public void translate() {
		assert(status == Status.RESOLVED_DASH);
		//System.out.println("Translating to Alloy");
		// this is so we can partition the translation
		// code into a different file
		// translation is done in place
		DashToAlloy.translate(this);
		// if no errors 
		status = Status.TRANSLATED_TO_ALLOY;
	}

    // for testing
    public List<String> getDefaults(String s) {
    	return stateTable.getDefaults(s);
    }


    public List<String> getAllEventNames() {
    	return eventTable.getAllEventNames();
    }
	public List<String> getAllInternalEventNames() {
		//assert(hasInternalEvents());
		return eventTable.getAllInternalEvents();
	}
	public List<String> getAllEnvironmentalEventNames() {
		//assert(hasExternalEvents());
		return eventTable.getAllEnvironmentalEvents();
	}
	


}