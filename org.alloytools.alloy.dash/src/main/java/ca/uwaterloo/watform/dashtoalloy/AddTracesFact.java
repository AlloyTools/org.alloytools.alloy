/*
	Add fact for traces
*/

package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
//import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import static ca.uwaterloo.watform.core.DashStrings.*;
//import ca.uwaterloo.watform.core.DashUtilFcns;
//import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
//import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import ca.uwaterloo.watform.alloyasthelper.DeclExt;

//import ca.uwaterloo.watform.alloyasthelper.DeclExt;
//import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddTracesFact {

	public static void addTracesFact(DashModule d) {

		/*
		open util/traces[Snapshot] as snapshot

		fact traces { 
			init[snapshot/first] and 
			(all s: one (Snapshot - snapshot/last) | small_step[s, s. (snapshot/next)] ) 
		}
		*/

		assert(DashOptions.isTraces);
        List<Expr> body = new ArrayList<Expr>();
 
        Expr snapShotFirst = createVar(snapshotName + "/" + tracesFirstName);
        Expr snapShotLast = createVar(snapshotName + "/" + tracesLastName);
        Expr snapShotNext = createVar(snapshotName + "/" + tracesNextName);

		List<Expr> args = new ArrayList<Expr>();
		args.add(snapShotFirst);
        body.add(createPredCall(initFactName,args));
        
        args = new ArrayList<Expr>();
        args.add(curVar());
        args.add(curJoinExpr(snapShotNext));
        List<Decl> decls = new ArrayList<Decl>();
        decls.add((Decl) new DeclExt(curName, createOne(createDiff(createVar(snapshotName), snapShotLast))));
        body.add(createAll(decls,createPredCall(smallStepName,args)));

        d.alloyString += d.addFactSimple(tracesFactName, body);

    }
}