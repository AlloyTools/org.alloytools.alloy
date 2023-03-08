/* string names used in Dash and conversion to Alloy */

package ca.uwaterloo.watform.core;

public class DashStrings {

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
	
	
	


	// used for translation to Alloy
	public static String qualChar = "/";
	// predicate names

	public static String smallStepName = "small_step";
	public static String stableName = "stable";
	public static String equalsName = "equals";
	public static String isEnabled = "isEnabled";
	
	// sig names
	public static String snapshotName = "Snapshot";
	public static String confName = "confName";
	public static String takenName = "taken";

	public static String stateLabelName = "StateLabel";
	public static String systemStateName = "SystemState";

	public static String bufferIndexName = "bufIndex";
	// how to name parameter variables
	public static String pName = "p";
	public static String eventsName = "events";
	public static String eventLabelName = "EventLabel";
	public static String envEventLabelName = "EnvironmentalEvent";
	public static String intEventLabelName = "InternalEvent";


	public static String preName = "_pre";
	public static String postName = "_post";
	public static String semanticsName = "_semantics";
	public static String testIfNextStableName = "testIfNextStable";
	public static String isEnabledAfterStep = "_ isEnabledAfterStep";
	public static String tName = "t";
	public static String geName = "ge";

	/* alloy keywords */
	public static String extendsName = "extends";
	public static String inName = "in";
	public static String abstractName = "abstract";
	public static String oneName = "one";
	public static String varName = "var";
	public static String boolName = "boolean";
	public static String intName = "int";
	public static String utilBooleanName = "util/boolean";
	public static String utilCTLpathName = "util/ctl_path";
	public static String utilOrderingName = "util/ordering";
	public static String utilBufferName = "util/buffer";

	public static String tracesName = "traces";
	
	public static String sCur = "s";
	public static String sNext = "sNext";
	public static String prime(String a) {
		return a+"'";
	};

	public static enum IntEnvKind {
		INT,
		ENV 
	}

	public static enum StateKind {
		AND,
		OR,
		BASIC
	}

	public static enum DefKind {
		DEFAULT,
		NOTDEFAULT
	}
}