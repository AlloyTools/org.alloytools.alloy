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

public class AddTraces {

	public static void addTracesFact(DashModule d) {

		/*
			open util/traces[Snapshot] as snapshot

			fact traces { 
				init[snapshot/first] and 
				(all s: Snapshot | small_step[s, s. (snapshot/next)] ) 
			}

			Note: previously this was
			(all s: one (Snapshot - snapshot/last) | small_step[s, s. (snapshot/next)]
			but this is NOT correct because the next relation must hold for the loop back
			to a previous state provided by the traces module
		*/

		assert(DashOptions.isTraces);
        List<Expr> body = new ArrayList<Expr>();
 
        Expr snapShotFirst = createVar(snapshotName + "/" + tracesFirstName);
        //Expr snapShotLast = createVar(snapshotName + "/" + tracesLastName);
        Expr snapShotNext = createVar(snapshotName + "/" + tracesNextName);

        
		List<Expr> args = new ArrayList<Expr>();
		args.add(snapShotFirst);
        body.add(createPredCall(initFactName,args));
        
        args = new ArrayList<Expr>();
        args.add(curVar());
        args.add(curJoinExpr(snapShotNext));
        
        List<Decl> decls = new ArrayList<Decl>();
        //decls.add((Decl) new DeclExt(curName, createOne(createDiff(createVar(snapshotName), snapShotLast))));
        decls.add((Decl) new DeclExt(curName, createVar(snapshotName)));
        body.add(createAll(decls,createPredCall(smallStepName,args)));

        d.alloyString += d.addFactSimple(tracesFactName, body);

    }


    public static void addTracesStrongNoStutterPred(DashModule d) {
	    /* 
	    	pred no_stutter {
	    		all s:DshSnapshot |
	        	s = first or NO_TRANS not in s.dsh_taken0
	    */
		assert(DashOptions.isTraces);
		Expr snapShotFirst = createVar(snapshotName + "/" + tracesFirstName);
        List<Expr> body = new ArrayList<Expr>();
        List<Decl> decls = new ArrayList<Decl>();
 
        List<Expr> bigOr = new ArrayList<Expr>();
        for (int i = 0; i <= d.getMaxDepthParams(); i++) {
        	// don't need to make this stronger than an Or
        	// b/c other parts of semantics will make sure only
        	// one transTaken is true
            bigOr.add(createNotIn(createVar(noTransName), curTransTaken(i)));
        }
        Expr ex = createOr(createEquals(curVar(), snapShotFirst), createOrList(bigOr));
        
        decls.add((Decl) new DeclExt(curName, createVar(snapshotName)));
        body.add(createAll(decls,ex));

        List<Decl> emptyDecls = new ArrayList<Decl>();
        d.alloyString += d.addPredSimple(strongNoStutterName, emptyDecls, body);

    }
}

