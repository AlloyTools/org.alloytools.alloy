/*
	Add fact for tcmc
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

public class AddTcmcFact {

	public static void addTcmcFact(DashModule d) {

		/*
		open util/tcmc[Snapshot] as snapshot

		fact tcmc { 
			// ksS0 satisfies init (initial) constraints 
			(all s: one Snapshot | { s in tcmc/ks_s0 } <=> init[s]) 
			// ksSigma satisfies small_step predicate 
			(all s,s_next: one Snapshot | ({ s -> s_next } in tcmc/ks_sigma) <=> small_step[s, s_next ]) 
		}

		*/

		assert(DashOptions.isTcmc);
        List<Expr> body = new ArrayList<Expr>();
 
 		List<Decl> decls = new ArrayList<Decl>();
 		decls.add(curDecl());

 		List<Expr> args = new ArrayList<Expr>();
 		args.add(curVar());
 		body.add(
 			createAll(
 				decls, 
 				createIff(
 					createIn(curVar(), createVar(tcmcKsS0Name)),
 					createPredCall(initFactName,args))));

 		body.add(
 			createAll(
	 			curNextDecls(), 
	 			createIff(
	 				createIn(
	 					createArrow(curVar(), nextVar()),
	 					createVar(tcmcKsSigmaName)),
	 				createPredCall(smallStepName, curNextVars()))));

        d.alloyString += d.addFactSimple(tcmcFactName, body);

    }
}