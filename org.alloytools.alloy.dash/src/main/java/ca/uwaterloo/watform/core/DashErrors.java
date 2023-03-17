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

	public static void stateNameCantBeFQN(Pos o, String name) throws Err {
		throw new ErrorSyntax(o,"State name "+name+" when declared cannot have slash");
	}
	public static void onlyOneState(Pos o) throws Err {
		throw new ErrorSyntax(o,"Model can only have one 'state' section");
	}
	public static void dupSiblingNames(String dups) throws Err {
		throw new ErrorSyntax("Duplicate sibling state names: " + dups);
	}
	public static void dupTransNames(String dups) throws Err {
		throw new ErrorSyntax("Duplicate sibling state names: " + dups);
	}
	public static void siblingsSameKind(String fqn) throws Err {
		throw new ErrorSyntax("Children of "+fqn+" must all be of concurrent or not concurrent");
	}
	public static void crossRefMoreThanOneArg(Pos o, String n) throws Err {
		throw new ErrorSyntax(o,"Two many args to reference to "+n+" in sibling state");
	}
	public static void moreThanOneSrcDest(String x, String n) throws Err {
		throw new ErrorSyntax("Transition "+n+" has more than one "+ x);
	}
	public static void noTrans() throws Err {
		throw new ErrorSyntax("Model does not contain any transitions.");
	}
	public static void transUsesNonExistentState(String n) throws Err {
		throw new ErrorSyntax("Some transition has from/goto to state "+n+" which doesn't exist");
	}
	public static void tooManyDefaults(String fqn) throws Err {
		throw new ErrorSyntax("State "+fqn+" has more than one default state");
	}
	public static void noDefaultState(String fqn) throws Err {
		throw new ErrorSyntax("State "+fqn+" does not have a default state");
	}
	public static void unknownSrcDest(String x, String t, String tfqn) throws Err {
		throw new ErrorSyntax("Trans "+tfqn+" "+t+" "+x+ " is unknown");
	}
	public static void ambiguousSrcDest(String x, String tfqn) throws Err {
		throw new ErrorSyntax("Trans "+tfqn+" "+x+" dest name is ambiguous: could be child of of parent state or sibling of parent state");
	}
	public static void andCrossTransition(String tfqn) throws Err {
		throw new ErrorSyntax("Trans "+tfqn+" goes between concurrent states");
	}

	// parts of the code that should be unreachable -------------

	public static void concStateNoChildren(String fqn) throws Err {
		throw new ErrorFatal("Concurrent state "+fqn+" must have substates");
	}
	public static void basicStateParam(String fqn) throws Err {
		throw new ErrorFatal("Basic state "+fqn+" has parameter");
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
	public static void missingExpr(String s) throws Err {
		throw new ErrorFatal("Missing expr type in "+s);
	}

}