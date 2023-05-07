/* 
 * All the errors that can be thrown in Dash code
 */

package ca.uwaterloo.watform.core;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;

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
	public static void dupTransNames(Pos o, String dups) throws Err {
		throw new ErrorSyntax(o, dupTransNameMsg + dups);
	}
	/*
	public static String moreThanOneSrcDestMsg = "Transition has more than one src or dest: ";
	public static void moreThanOneSrcDest(String x, String n) throws Err {
		throw new ErrorSyntax(moreThanOneSrcDestMsg + x);
	}
	*/
	public static String unknownSrcDestMsg = "Src/Dest of trans is unknown: ";
	public static void unknownSrcDest(String x, String t, String tfqn) throws Err {
		throw new ErrorSyntax(unknownSrcDestMsg + "trans "+tfqn+" "+t+" "+x);
	}
	public static String fqnSrcDestMustHaveRightNumberParamsMsg = "Incorrect number of parameters: ";
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

	public static String nameShouldNotBePrimedMsg = "Declared state/trans/event/var cannot have a primed name: ";
	public static void nameShouldNotBePrimed(String n) {
		throw new ErrorSyntax(nameShouldNotBePrimedMsg+n);
	}
	public static String transNameCantBeFQNMsg = "Trans name cannot be fully qualified at declaration: ";
	public static void transNameCantBeFQN(Pos o, String s) {
		throw new ErrorSyntax(o, transNameCantBeFQNMsg + s);
	}

	public static String eventNameCantBeFQNMsg = "Event name cannot be fully qualified at declaration: ";
	public static void eventNameCantBeFQN(Pos o, String s) {
		throw new ErrorSyntax(o, eventNameCantBeFQNMsg + s);
	}
	public static String duplicateEventNameMsg = "Event name already in use: ";
	public static void duplicateEventName(Pos o, String s) {
		throw new ErrorSyntax(o, duplicateEventNameMsg + s);
	}
	public static String varNameCantBeFQNMsg = "Var name cannot be fully qualified at declaration: ";
	public static void varNameCantBeFQN(Pos o, String s) {
		throw new ErrorSyntax(o, varNameCantBeFQNMsg + s);
	}
	public static String duplicateVarNameMsg = "Var name already in use: ";
	public static void duplicateVarName(Pos o, String s) {
		throw new ErrorSyntax(o, duplicateVarNameMsg + s);
	}
	public static String bufferNameCantBeFQNMsg = "Buffer name cannot be fully qualified at declaration: ";
	public static void bufferNameCantBeFQN(Pos o, String s) {
		throw new ErrorSyntax(o, bufferNameCantBeFQNMsg + s);
	}
	public static String duplicateBufferNameMsg = "Buffer name already in use: ";
	public static void duplicateBufferName(Pos o, String s) {
		throw new ErrorSyntax(o, duplicateBufferNameMsg + s);
	}

	// event errors
	public static String tooManyMsg = "Multiple ";
	public static void tooMany(String xType, String tfqn) {
		throw new ErrorSyntax(tooManyMsg + xType + " in " + tfqn);
	}
	public static String unknownEventMsg = "Event does not exist: ";
	public static void unknownEvent(String xType, String v, String tfqn) {
		throw new ErrorSyntax(unknownEventMsg +v+" in "+ tfqn +" "+ xType);
	}
	public static String ambiguousEventMsg = "Event name not unique within this conc/Root region: ";
	public static void ambiguousEvent(String xType, String v, String tfqn) {
		throw new ErrorSyntax(ambiguousEventMsg +v+" in "+ tfqn + " "+xType);
	}
	public static String fqnEventMissingParametersMsg = "Fully qualified event name missing paramaters: ";
	public static void fqnEventMissingParameters(String xType, String v, String tfqn) {
		throw new ErrorSyntax(fqnEventMissingParametersMsg + v + " in "+tfqn + " " + xType);
	}
	public static String expNotEventMsg = "Not an event for: ";
	public static void expNotEvent(String xType, String tfqn) {
		throw new ErrorSyntax(expNotEventMsg + tfqn + " " + xType);
	}
	//public static void siblingsSameKind(String fqn) throws Err {
	//	throw new ErrorSyntax("Children of "+fqn+" must all be of concurrent or not concurrent");
	//}
	//public static void crossRefMoreThanOneArg(Pos o, String n) throws Err {
	//	throw new ErrorSyntax(o,"Two many args to reference to "+n+" in sibling state");
	//}
	public static String noPrimedVarsInMsg = "Primed variables are not allowed in: ";
	public static void noPrimedVarsIn(String s1, String s2, String s3) {
		throw new ErrorSyntax(noPrimedVarsInMsg + s1 + " " + s2 + " "+s3);
	}
	public static String ambiguousVarMsg = "Var name not unique within this conc/Root region: ";
	public static void ambiguousVar(String xType, String v, String tfqn) {
		throw new ErrorSyntax(ambiguousVarMsg +v+" in "+ tfqn + " "+xType);
	}
	public static String fqnVarWrongNumberParametersMsg = "Wrong number of parameter values for: ";
	public static String fqnVarWrongNumberParameters(String s1, String s2, String s3) {
		throw new ErrorSyntax(fqnVarWrongNumberParametersMsg + s1 + " "+s2 +" "+s3);
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
	public static void varDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", var "+n+ " does not exist in var table");
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
	public static String chopPrefixFromFQNwithNoPrefixMsg = "chopPrefixFromFQNwithNoPrefix: ";
	public static void chopPrefixFromFQNwithNoPrefix(String s) throws Err {
		throw new ErrorFatal(chopPrefixFromFQNwithNoPrefixMsg + s);
	}
	public static void nonEmptyStateItems() throws Err {
		throw new ErrorFatal("Non-empty state items at end of state resolve");
	}
	public static void nonEmptyTransItems() throws Err {
		throw new ErrorFatal("Non-empty trans items at end of trans resolve");
	}
	public static void getRightNotBinaryOrJoin(String s) throws Err {
		throw new ErrorFatal("getRightNotBinaryOrJoin: "+s);
	}
	public static void getLeftNotBinaryOrJoin(String s) throws Err {
		throw new ErrorFatal("getLeftNotBinaryOrJoin: "+s);
	}
	public static void getSubNotUnary(String s) throws Err {
		throw new ErrorFatal("getSubNotUnary: "+s);
	}
	public static void replaceDashRefExprVarError() throws Err {
		throw new ErrorFatal("replaceDashRefExprVarError");
	}
	public static void nonDashRefExpr() throws Err {
		throw new ErrorFatal("nonDashRefExpr");
	}
	public static void eventTableEventNotFound(String m, String efqn) {
		throw new ErrorFatal("eventTableEventNotFound: "+m+" "+efqn);
	}
	public static void regionMatchesWrongParamNumber() {
		throw new ErrorFatal("regionMatchesWrongParamNumber");
	}
	public static void createTestIfNextStableCallMultipleScopesAtSameLevel() {
		throw new ErrorFatal("createTestIfNextStableCallMultipleScopesAtSameLevel");
	}
	public static String UnsupportedExpr(String s1, String s2) {
		throw new ErrorFatal("unsupported expression type in: "+ s1 + " "+s2);
	}
	public static String UnsupportedExpr(String s1, Expr e) {
		throw new ErrorFatal("unsupported expression type in: "+ s1+ " " + e.toString());
	}
}