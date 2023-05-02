package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashRef;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddTestIfNextStable {

	// only one per module
	public static void addTestIfNextStable(DashModule d) {
		List<Decl> decls = new ArrayList<Decl>();
		List<Expr> args = new ArrayList<Expr>();
		List<Expr> body = new ArrayList<Expr>();
		if (!DashOptions.isElectrum) {
			decls.addAll(curNextDecls());
			args.addAll(curNextVars());
		}
		for (int i=0; i<= d.getMaxDepthParams(); i++) {
			decls.add(scopeDecl(i));
			args.add(scopeVar(i));
			if (d.hasEventsAti(i)) {
				decls.add(genEventDecl(i));
				args.add(genEventVar(i));
			}
		}
		for (String tfqn: d.getAllTransNames()) {
			String tout = translateFQN(tfqn);
			body.add(createNot(
					createPredCall(tout + DashStrings.enabledAfterStepName, args)));
		}

		d.alloyString += d.addPredSimple(DashStrings.testIfNextStableName,decls,body);
	}
}