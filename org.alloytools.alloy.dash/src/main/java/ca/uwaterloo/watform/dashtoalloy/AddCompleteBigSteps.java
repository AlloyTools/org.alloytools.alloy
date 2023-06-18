/*
 * completeBigStepsFact
 *
 * Every non-stable snapshot included in the next snapshot relation 
 * has a next snapshot, which means every big step must be complete.
 * fact completeBigSteps { 
 *      all s : Snapshot | s.stable == False => some s': Snapshot. small_step[s,s']
 * }
 *
 * The above works for all methods.
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

public class AddCompleteBigSteps {

	public static void addCompleteBigSteps(DashModule d) {
		if (d.hasConcurrency()) {
			Expr b = createAll(curDecls(),
						createImplies(
							curStableFalse(),
							createSome(nextDecls(), 
								createPredCall(DashStrings.smallStepName, curNextVars()))));

			List<Expr> body = new ArrayList<Expr>();
			body.add(b);
			d.alloyString += d.addFactSimple(DashStrings.completeBigStepsName, body);
		}
	}
}
