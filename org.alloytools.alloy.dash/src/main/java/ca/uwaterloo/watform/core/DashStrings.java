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

	public static String utilTcmcPathName = "util/tcmc_path";
	public static String tcmcKsSigmaName = "tcmc/ks_sigma";
	public static String tcmcKsS0Name = "tcmc/ks_s0";	


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

	// init is a reserved word in Dash
	public static String initFactName = "dsh_initial";
	public static String electrumInitName = "dsh_init";
	// predicate names

	public static String smallStepName = "dsh_small_step";
	public static String stableName = "dsh_stable";
	//public static String equalsName = "equals";
	public static String isEnabled = "dsh_isEnabled";
	public static String tracesFactName = "dsh_traces_fact";
	public static String electrumFactName = "dsh_electrum_fact";
	public static String tcmcFactName = "dsh_tcmc_fact";


	/* names used in Dash translation */
	// sig names
	public static String snapshotName = "DshSnapshot";
	public static String allEventsName = "DshEvents";
	public static String allEnvironmentalEventsName = "DshEnvEvents";
	public static String allInternalEventsName = "DshIntEvents";
	public static String variablesName = "DshVars";
	public static String stateLabelName = "DshStates";
	//public static String systemStateName = "SystemState";
	//public static String transitionLabelName = "TransitionLabel";
	public static String identifierName = "DshIds";
	public static String bufferName = "DshBuffer";

	// field names
	public static String confName = "dsh_conf";
	public static String scopesUsedName = "dsh_sc_used";
	public static String eventsName = "dsh_events";
	
	// predicate names
	//public static String tName = "dsh_t";
	public static String preName = "_pre";
	public static String postName = "_post";
	//public static String semanticsName = "_semantics";
	public static String testIfNextStableName = "_testIfNextStable";
	public static String enabledAfterStepName = "_enabledAfterStep";
	
	// variable/parameter names
	// how to name parameter variables
	public static String curName = "s";
	public static String nextName = "sn";
	public static String pName = "p";
	public static String genEventName = "dsh_genEvs";
	public static String scopeName = "dsh_scp";

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