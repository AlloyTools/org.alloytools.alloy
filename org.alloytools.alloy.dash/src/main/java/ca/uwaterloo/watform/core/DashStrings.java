 /* string names used in Dash and conversion to Alloy */

package ca.uwaterloo.watform.core;

public class DashStrings {

	/* alloy keywords */
	public static String moduleName = "module";
	public static String extendsName = "extends";
	public static String inName = "in";
	public static String abstractName = "abstract";
	public static String oneName = "one";
	public static String varName = "var";
	public static String openName = "open";
	public static String asName = "as";
	public static String boolName = "boolean/Bool";
	public static String trueName = "boolean/True";
	public static String falseName = "boolean/False";
	public static String noneName = "none";
	public static String intName = "int";
	public static String utilBooleanName = "util/boolean";
	public static String utilCTLpathName = "util/ctl_path";
	public static String utilOrderingName = "util/ordering";
	public static String utilBufferName = "util/buffer";
	public static String sigName = "sig";
	public static String predName = "pred";
	
	// used for printing: parts of Dash syntax
	// must be in sync with Dash-cup-symbols.txt
	public static String stateName = "state";
	public static String concName = "conc";
	public static String defaultName = "default";

	public static String eventName = "event";
	public static String envName = "env";
	public static String bufName = "buf";

	public static String initName = "init";
	public static String invariantName = "inv";
	public static String actionName = "action";
	public static String conditionName = "condition";

	public static String transName = "trans";
	public static String fromName = "from";
	public static String onName = "on";
	public static String whenName = "when";
	public static String doName = "do";
	public static String gotoName = "goto";
	public static String sendName = "send";
	public static String SLASH = "/";
	
	

	// predicate names

	public static String smallStepName = "small_step";
	public static String stableName = "stable";
	public static String equalsName = "equals";
	public static String isEnabled = "isEnabled";
	
	// sig/field names
	public static String snapshotName = "Snapshot";
	public static String confName = "conf";
	public static String scopesUsedName = "scopesUsed";

	public static String stateLabelName = "StateLabel";
	public static String systemStateName = "SystemState";
	//public static String transitionLabelName = "TransitionLabel";
	public static String identifierName = "Identifiers";
	// how to name parameter variables
	public static String pName = "p";
	public static String eventsName = "events";
	public static String allEventsName = "AllEvents";
	public static String allEnvironmentalEventsName = "AllEnvironmentalEvents";
	public static String allInternalEventsName = "AllInternalEvent";


	public static String preName = "_pre";
	public static String postName = "_post";
	public static String semanticsName = "_semantics";
	public static String testIfNextStableName = "testIfNextStable";
	public static String enabledAfterStepName = "_enabledAfterStep";
	public static String tName = "t";
	public static String genEventName = "genEvents";
	public static String scopeName = "scope";
	public static String bufferName = "buffer";
	public static String bufferIndexName = "bufIdx";



	public static String tracesName = "traces";
	
	public static String curName = "s";
	public static String nextName = "sNext";
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

	public static String processRef = "$$PROCESSREF$$";

}