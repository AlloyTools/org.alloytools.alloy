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

			fact dsh_traces_fact {
			  DshSnapshot/first.dsh_initial
			  (some DshSnapshot/back) =>
				  (all s: DshSnapshot | (s.DshSnapshot/next).(s.dsh_small_step))
			  else 
				(all s:DshSnapshot - last | (s.DshSnapshot/next).(s.dsh_small_step))
			}

			"back" is the DshSnapshot that is looped back to in the trace to
			make it infinite
			"next" is the "Next" relation in traces plus the loop.  If back is empty,
			loop is empty and next=Next.  If back is a DshSnapshot, loop exists and 
			next=Next+loop
			To permit both infinite and finite traces we have to have
			the two cases above.
			If we only have the if-clause above, then the "last" Snapshot must have a next
			forcing all traces to be infinite.

		*/

		assert(DashOptions.isTraces);
        List<Expr> body = new ArrayList<Expr>();
 
        Expr snapShotFirst = createVar(snapshotName + "/" + tracesFirstName);
        Expr snapShotLast = createVar(snapshotName + "/" + tracesLastName);
        Expr snapShotNext = createVar(snapshotName + "/" + tracesNextName);
        Expr snapshotBack = createVar(snapshotName + "/" + tracesBackName);
        
		List<Expr> args = new ArrayList<Expr>();
		args.add(snapShotFirst);
        body.add(createPredCall(initFactName,args));
        
        args = new ArrayList<Expr>();
        args.add(curVar());
        args.add(curJoinExpr(snapShotNext));

        List<Decl> decls1 = new ArrayList<Decl>();
        decls1.add((Decl) new DeclExt(curName, createVar(snapshotName)));

        List<Decl> decls2 = new ArrayList<Decl>();
        decls2.add((Decl) new DeclExt(curName, createOne(createDiff(createVar(snapshotName), snapShotLast))));

        body.add(createITE(
        	createSomeOf(snapshotBack),
        	createAll(decls1,createPredCall(smallStepName,args)),
        	createAll(decls2,createPredCall(smallStepName,args))
        ));

        d.alloyString += d.addFactSimple(tracesFactName, body);

    }


    public static void addStrongNoStutterPred(DashModule d) {
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
            bigOr.add(createNot(createEquals(curTransTaken(i),createNoneArrow(i))));
        }
        Expr ex = createOr(createEquals(curVar(), snapShotFirst), createOrList(bigOr));
        
        decls.add((Decl) new DeclExt(curName, createVar(snapshotName)));
        body.add(createAll(decls,ex));

        List<Decl> emptyDecls = new ArrayList<Decl>();
        d.alloyString += d.addPredSimple(strongNoStutterName, emptyDecls, body);

    }
}

