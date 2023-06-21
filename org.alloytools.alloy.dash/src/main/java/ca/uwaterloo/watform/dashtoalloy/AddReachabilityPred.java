/*
 *
 * Every snapshot is reachable from an initial snapshot 
 * fact reachabilityAxiom { 
 *      all s : Snapshot | s in Snapshot .(( initial) <: * (sigma)) 
 * }
 */

package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.IntStream;

import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddReachabilityPred {

	public static void addReachabilityPred(DashModule d) {
		assert(!DashOptions.isElectrum && !DashOptions.isTraces);
		Expr b = createAll(curDecls(), 
				createIn(curVar(),
					createJoin(createVar(DashStrings.snapshotName),
					createDomainRes(createVar(DashStrings.tcmcInitialStateName), 
						createReflexiveTransitiveClosure(createVar(DashStrings.tcmcSigmaName))))));
		List<Expr> body = new ArrayList<Expr>();
		body.add(b);
		List<Decl> emptyDecls = new ArrayList<Decl>();
		d.alloyString += d.addPredSimple(DashStrings.reachabilityName, emptyDecls, body);
	}
}
