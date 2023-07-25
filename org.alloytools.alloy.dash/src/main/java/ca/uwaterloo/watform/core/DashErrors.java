/* 
 * All the errors that can be thrown in Dash code
 */

package ca.uwaterloo.watform.core;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashUtilFcns;

public class DashErrors {

	// syntax errors --------------------------------------------

	public static String statesNotEnteredMsg = "The following states are not entered: ";
	public static void statesNotEntered(List<String> statesNotEntered) {
		throw new ErrorSyntax(statesNotEnteredMsg + DashUtilFcns.strCommaList(statesNotEntered));
	}
	public static String intEventsNotGeneratedMsg = "The following internal events are never generated: ";
	public static void intEventsNotGenerated(List<String> intEventsNotGenerated) {
		throw new ErrorSyntax(intEventsNotGeneratedMsg + DashUtilFcns.strCommaList(intEventsNotGenerated));
	}
	public static String envEventsNotUsedMsg = "The following environmental events are never used: ";
	public static void envEventsNotUsed(List<String> envEventsNotUsed) {
		throw new ErrorSyntax(envEventsNotUsedMsg + DashUtilFcns.strCommaList(envEventsNotUsed));
	}
	public static String onlyOneStateMsg = "Dash model can only have one 'state' section";
	public static void onlyOneState(Pos o) throws Err {
		throw new ErrorSyntax(o,onlyOneStateMsg);
	}
	public static String noTransMsg = "Dash Model does not contain any transitions.";
	public static void noTrans() throws Err {
		throw new ErrorSyntax(noTransMsg);
	}
	public static String noStatesMsg = "Dash model must have at least one state.";
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
	public static String nameCantBeFQNMsg = "When declared, name cannot have slash: ";
	public static void nameCantBeFQN(Pos o, String name) throws Err {
		throw new ErrorSyntax(o,nameCantBeFQNMsg+name);
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
	public static String ambiguousRefMsg = "Name not unique: ";
	public static void ambiguousRef(Pos pos, String expString) throws Err {
		throw new ErrorSyntax(pos + " " + ambiguousRefMsg + expString);
	}

	// below this have not been tested
	public static String unknownStateMsg = "State does not exist: ";
	public static void unknownState(Pos pos, String expString) {
		throw new ErrorSyntax(pos + " " + unknownStateMsg + expString);
	}
	public static String unknownEventMsg = "Event does not exist: ";
	public static void unknownEvent(Pos pos, String expString) {
		throw new ErrorSyntax(pos + " " + unknownEventMsg + expString);
	}
	
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
	public static String duplicateNameMsg = "Name already in use: ";
	public static void duplicateName(Pos o, String s) {
		throw new ErrorSyntax(o, duplicateNameMsg + s);
	}

	// event errors
	public static String tooManyMsg = "Multiple ";
	public static void tooMany(String xType, String tfqn) {
		throw new ErrorSyntax(tooManyMsg + xType + " in " + tfqn);
	}
	public static String cantSendAnEnvEventMsg = " can't send an environmental event: ";
	public static void cantSendAnEnvEvent(Pos p, String expString) {
		throw new ErrorSyntax(p + cantSendAnEnvEventMsg + expString);
	}
	/*
	public static String ambiguousEventMsg = "Event name not unique within this conc/Root region: ";
	public static void ambiguousEvent(String xType, String v, String tfqn) {
		throw new ErrorSyntax(ambiguousEventMsg +v+" in "+ tfqn + " "+xType);
	}
	*/
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
	public static String noPrimedVarsMsg = " Primed variables are not allowed in: ";
	public static void noPrimedVars(Pos pos, String expString) {
		throw new ErrorSyntax(pos + " " + noPrimedVarsMsg + expString);
	}
	public static String ambiguousVarMsg = "Var name not unique within this conc/Root region: ";
	public static void ambiguousVar(String xType, String v, String tfqn) {
		throw new ErrorSyntax(ambiguousVarMsg +v+" in "+ tfqn + " "+xType);
	}
	public static String fqnVarWrongNumberParametersMsg = "Wrong number of parameter values for: ";
	public static String fqnVarWrongNumberParameters(String s1, String s2, String s3) {
		throw new ErrorSyntax(fqnVarWrongNumberParametersMsg + s1 + " "+s2 +" "+s3);
	}

	public static String cantPrimeAnExternalVarMsg = " Internal var/buffer cannot be primed: ";
	public static String cantPrimeAnExternalVar(Pos pos, String expString) {
		throw new ErrorSyntax(pos + " " + cantPrimeAnExternalVarMsg + expString);
	}
	public static String emptyModuleMsg = "Empty module";
	public static String emptyModule() {
		throw new ErrorSyntax(emptyModuleMsg);
	}
	public static String emptyFileMsg = "Empty file: ";
	public static String emptyFile(String fname) {
		throw new ErrorSyntax(emptyFileMsg+fname);
	}
	public static String ambiguousUseOfThisMsg = " Ambiguous use of 'this' ";
	public static String ambiguousUseOfThis(Pos pos, String expString) {
		throw new ErrorSyntax(pos + ambiguousUseOfThisMsg + expString);
	}
	public static String nonParamUseOfThisMsg = " 'this' must refer to a parametrized state: ";
	public static String nonParamUseOfThis(Pos pos, String expString) {
		throw new ErrorSyntax(pos + nonParamUseOfThisMsg + expString);
	}
	public static String wrongNumberParamsMsg = " Incorrect number of parameters: ";
	public static void wrongNumberParams(Pos pos, String expString) {
		throw new ErrorSyntax(pos + " " + wrongNumberParamsMsg + expString);
	}
	public static String varPredOverlapMsg = "Same name used for dynamic variable and Dash predicate: ";
	public static void varPredOverlap(List<String> s) {
		throw new ErrorSyntax(varPredOverlapMsg + s);
	}
	// parts of the code that should be unreachable -------------

	public static String ancesNotPrefixMsg = " must be a prefix of ";
	public static void ancesNotPrefix(String a, String d) throws Err {
		throw new ErrorFatal(a + ancesNotPrefixMsg + d);
	}
	public static String notVarBeforeDashRefMsg = "must be var: ";
	public static void notVarBeforeDashRef (Pos o, String expString) {
		throw new ErrorFatal(o + notVarBeforeDashRefMsg + expString);
	}
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
	public static void predDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", var "+n+ " does not exist in pred table");
	}
	public static void bufferDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", buffer "+n+ " does not exist in buffer table");
	}
	public static void varBufferDoesNotExist(String s1, String n) throws Err {
		throw new ErrorFatal("for function "+s1+", "+n+ " does not exist in buffer or var table");
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
	public static void nonEmptyStateItems(List<Object> x) throws Err {
		throw new ErrorFatal("Non-empty state items at end of state resolve: " + x);
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

	public static void createTestIfNextStableCallMultipleScopesAtSameLevel() {
		throw new ErrorFatal("createTestIfNextStableCallMultipleScopesAtSameLevel");
	}
	public static String UnsupportedExpr(String s1, String s2) {
		throw new ErrorFatal("unsupported expression type in: "+ s1 + " "+s2);
	}
	public static String UnsupportedExpr(String s1, Expr e) {
		throw new ErrorFatal("unsupported expression type in: "+ s1+ " " + e.toString());
	}
	public static void bufferIndexDoesNotMatchBufferNumber() {
		throw new ErrorFatal("bufferIndexDoesNotMatchBufferNumber");
	}
	public static void doesNotExist(String fcnName, String m) {
		throw new ErrorFatal("fcn "+fcnName+" arg "+m+"not in table");
	}
	public static void noInitialEntered(){
		throw new ErrorFatal("there are no default initial states");
	}
	public static void sistersDontChangeDoesNotHaveParams(String s) {
		throw new ErrorFatal("sistersDontChangeDoesNotHaveParams: "+s);
	}
	public static void hasSpecificParamValues() {
		throw new ErrorFatal("hasSpecificParamValues");
	}
}