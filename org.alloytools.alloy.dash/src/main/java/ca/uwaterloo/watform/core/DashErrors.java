/* 
 * All the errors that can be thrown in Dash code
 */

package ca.uwaterloo.watform.core;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorFatal;

public class DashErrors {

	// syntax errors --------------------------------------------

	public static String onlyOneStateMsg = "Model can only have one 'state' section";
	public static void onlyOneState(Pos o) throws Err {
		throw new ErrorSyntax(o,onlyOneStateMsg);
	}
	public static String noTransMsg = "Model does not contain any transitions.";
	public static void noTrans() throws Err {
		throw new ErrorSyntax(noTransMsg);
	}
	public static String noStatesMsg = "Model must have at least one state.";
	public static void noStates() throws Err {
		throw new ErrorSyntax(noStatesMsg);
	}
	public static String tooManyDefaultStatesMsg = "Too many default states in state: "; 
	public static void tooManyDefaults(String fqn) throws Err {
		throw new ErrorSyntax(tooManyDefaultStatesMsg+fqn);
	}
	public static String noDefaultStateMsg = "State does not have default state: ";
	public static void noDefaultState(String fqn) throws Err {
		throw new ErrorSyntax(noDefaultStateMsg+fqn);
	}
	public static String allConcDefaultStatesMsg = "All conc children of state must be defaults if one is for state: ";
	public static void allAndDefaults(String sfqn) throws Err {
		throw new ErrorSyntax(allConcDefaultStatesMsg+sfqn);
	}
	public static String stateNameCantBeFQNMsg = "When declared, state name cannot have slash: ";
	public static void stateNameCantBeFQN(Pos o, String name) throws Err {
		throw new ErrorSyntax(o,stateNameCantBeFQNMsg+name);
	}
	public static String dupSiblingNamesMsg = "Duplicate sibling state names: ";
	public static void dupSiblingNames(String dups) throws Err {
		throw new ErrorSyntax(dupSiblingNamesMsg + dups);
	}
	public static String dupTransNameMsg = "Duplicate transition names: ";
	public static void dupTransNames(String dups) throws Err {
		throw new ErrorSyntax(dupTransNameMsg + dups);
	}
	public static String moreThanOneSrcDestMsg = "Transition has more than one src or dest: ";
	public static void moreThanOneSrcDest(String x, String n) throws Err {
		throw new ErrorSyntax(moreThanOneSrcDestMsg + x);
	}
	public static String unknownSrcDestMsg = "Src/Dest of trans is unknown: ";
	public static void unknownSrcDest(String x, String t, String tfqn) throws Err {
		throw new ErrorSyntax(unknownSrcDestMsg + "trans "+tfqn+" "+t+" "+x);
	}
	public static String fqnSrcDestMustHaveRightNumberParamsMsg = "A fully qualified state name must have the right number of parameters: ";
	public static void fqnSrcDestMustHaveRightNumberParams(String xType, String tfqn) throws Err {
		throw new ErrorSyntax(fqnSrcDestMustHaveRightNumberParamsMsg + xType + " of transition "+ tfqn );
	}
	public static String srcDestCantHaveParamMsg = "Non-fully qualified src/dest cannot have parameters: ";
	public static void srcDestCantHaveParam(String xType, String tfqn) throws Err {
		throw new ErrorSyntax(srcDestCantHaveParamMsg + xType + " of transition "+ tfqn );
	}
	public static String ambiguousSrcDestMsg = "State name not unique within this conc/Root region: ";
	public static void ambiguousSrcDest(String x, String tfqn) throws Err {
		throw new ErrorSyntax(ambiguousSrcDestMsg + "trans "+tfqn+" "+x);
	}
	// below this have not been tested


	public static void siblingsSameKind(String fqn) throws Err {
		throw new ErrorSyntax("Children of "+fqn+" must all be of concurrent or not concurrent");
	}
	public static void crossRefMoreThanOneArg(Pos o, String n) throws Err {
		throw new ErrorSyntax(o,"Two many args to reference to "+n+" in sibling state");
	}


	public static void transUsesNonExistentState(String n) throws Err {
		throw new ErrorSyntax("Some transition has from/goto to state "+n+" which doesn't exist");
	}



	public static void andCrossTransition(String tfqn) throws Err {
		throw new ErrorSyntax("Trans "+tfqn+" goes between concurrent states");
	}




	// parts of the code that should be unreachable -------------

	public static String ancesNotPrefixMsg = " must be a prefix of ";
	public static void ancesNotPrefix(String a, String d) throws Err {
		throw new ErrorFatal(a + ancesNotPrefixMsg + d);
	}


	// not tested below this line
	public static void toAlloyNoDash() throws Err {
		throw new ErrorFatal("Translating to Alloy when no Dash part");
	}
	public static void addStateToStateTableDup(String fqn)  throws Err {
		throw new ErrorFatal(fqn + "entered more than once in StateTable");
	}
	public static void nonBasicEmptyChildren(String fqn) throws Err {
		throw new ErrorFatal(fqn + " empty children for non-basic state");
	}
	public static void isBasicNotExist(String q) throws Err {
		throw new ErrorFatal(q + " isBasicState of state that does not exist");
	}
	public static void transTableDup(String n) throws Err {
		throw new ErrorFatal("tried to add trans "+n+" to trans table twice");
	}
	public static void stateDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", state "+n+ " does not exist in state table");
	}
	public static void transDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", trans "+n+ " does not exist in trans table");
	}
	public static void missingExpr(String s) throws Err {
		throw new ErrorFatal("Missing expr type in "+s);
	}
	public static void tooHighParamDepth() throws Err {
		throw new ErrorFatal("paramsDepthInUse called with too high a number");
	}
	public static String paramNumberProblemMsg = "wrong number of param values: ";
	public static void paramNumberProblem(String s) throws Err {
		throw new ErrorFatal(paramNumberProblemMsg + s);
	}
}