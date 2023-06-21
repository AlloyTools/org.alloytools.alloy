 /* string names used in Dash and conversion to Alloy */

package ca.uwaterloo.watform.core;

public class DashStrings {

	// pretty printing anywhere
	public static String tab = "  ";

	/* alloy keywords */
	public static String moduleName = "module";
	public static String extendsName = "extends";
	public static String inName = "in";
	public static String abstractName = "abstract";
	public static String oneName = "one";
	public static String loneName = "lone";
	public static String varName = "var";
	public static String openName = "open";
	public static String asName = "as";

	public static String noneName = "none";
	public static String intName = "int";
	public static String sigName = "sig";
	public static String predName = "pred";
	public static String factName = "fact";
	public static String thisName = "this";


	// standard modules
	public static String utilBooleanName = "util/boolean";
	public static String boolName = "boolean/Bool";
	public static String trueName = "boolean/True";
	public static String falseName = "boolean/False";
	public static String isTrue = "boolean/isTrue";
	public static String isFalse = "boolean/isFalse";

	//public static String utilOrderingName = "util/ordering";
	public static String utilTracesName = "util/traces";
	public static String tracesFirstName = "first";
	public static String tracesNextName = "next";
	public static String tracesLastName = "last";

	public static String utilBufferName = "util/buffer";

	public static String utilTcmcPathName = "util/tcmc";
	public static String tcmcInitialStateName = "tcmc/ks_s0";	
	public static String tcmcSigmaName = "tcmc/ks_sigma";



	// Dash input keywords
	// used for printing: parts of Dash syntax
	// must be in sync with Dash-cup-symbols.txt
	public static String stateName = "state";
	public static String concName = "conc";
	public static String defaultName = "default";
	public static String eventName = "event";
	public static String envName = "env";
	public static String bufName = "buf";
	public static String transName = "trans";
	public static String fromName = "from";
	public static String onName = "on";
	public static String whenName = "when";
	public static String doName = "do";
	public static String gotoName = "goto";
	public static String sendName = "send";
	public static String invName = "inv";
	public static String enterName = "enter";
	public static String exitName = "exit";
	public static String initName = "init";
	

	// user must be aware of this name
	public static String bufferIndexName = "bufIdx";

	public static String dsh_prefix = "dsh_";
	// init is a reserved word in Dash
	public static String initFactName = dsh_prefix + "initial";
	public static String electrumInitName = dsh_prefix + "init";
	// predicate names

	public static String smallStepName = dsh_prefix + "small_step";
	public static String stableName = dsh_prefix + "stable";
	public static String stutterName = dsh_prefix + "stutter";
	//public static String equalsName = "equals";
	public static String isEnabled = dsh_prefix + "isEnabled";
	public static String tracesFactName = dsh_prefix + "traces_fact";
	public static String electrumFactName = dsh_prefix + "electrum_fact";
	public static String tcmcFactName = dsh_prefix + "tcmc_fact";
	public static String singleEventName = dsh_prefix + "single_event";
	public static String reachabilityName = dsh_prefix + "reachability";
	public static String enoughOperationsName = dsh_prefix + "enough_operations";
	public static String completeBigStepsName = dsh_prefix + "complete_big_steps";
	/* names used in Dash translation */
	// sig names
	public static String DshPrefix = "Dsh";
	public static String snapshotName = DshPrefix + "Snapshot";
	public static String allEventsName = DshPrefix + "Events";
	public static String allEnvironmentalEventsName = DshPrefix + "EnvEvents";
	public static String allInternalEventsName = DshPrefix + "IntEvents";
	public static String variablesName = DshPrefix + "Vars";
	public static String stateLabelName = DshPrefix + "States";
	public static String scopeLabelName = DshPrefix + "Scopes";
	//public static String systemStateName = "SystemState";
	public static String transitionLabelName = "Transitions";
	public static String identifierName = DshPrefix + "Ids";
	public static String bufferName = DshPrefix + "Buffer";
	public static String scopeSuffix = "Scope";

	// field names
	public static String confName = dsh_prefix + "conf";
	public static String scopesUsedName = dsh_prefix + "sc_used";
	public static String eventsName = dsh_prefix + "events";
	public static String transTakenName = dsh_prefix + "taken";
	// predicate names
	//public static String tName = "dsh_t";
	public static String preName = "_pre";
	public static String postName = "_post";
	//public static String semanticsName = "_semantics";
	public static String testIfNextStableName = "_nextIsStable";
	public static String enabledAfterStepName = "_enabledAfterStep";
	public static String allSnapshotsDifferentName = "allSnapshotsDifferent";
	// variable/parameter names
	// how to name parameter variables
	public static String curName = "s";
	public static String nextName = "sn";
	public static String pName = "p";
	public static String genEventName = "genEvs";
	public static String scopeName = "sc";
	public static String randomParamExt = "_aa";

	// strings used internally
	public static String processRef = "$$PROCESSREF$$";
	public static String SLASH = "/";
	public static String PRIME = "'";
	
	public static String prime(String a) {
		return a+"'";
	};

	public static enum IntEnvKind {
		INT,
		ENV 
	}

	public static enum StateKind {
		AND,
		OR   
		// basic is determined if no children
	}

	// this distinct is only used at parsing
	// within StateTable the default of a state is String name
	// or null
	public static enum DefKind {
		DEFAULT,
		NOTDEFAULT
	}


	public static boolean hasPrime(String s) {
		return (s.substring(s.length()-1, s.length()).equals(PRIME));
	}
	public static String removePrime(String s) {
		if (hasPrime(s)) return s.substring(0, s.length()-1);
		else return s;
	}

	
}