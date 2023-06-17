/*
 * Optional fact for single "input" assumption
 * For Dash+, this means only one env event per big step
 *
 *
 *
 *  fact single_input {
 *      all s: Snapshot |
 *           lone s.events0 :> ExternalEvents and no s.events1:> ExternalEvents and no.events2:> ExternalEvents or ...
 *           no s.events0:> ExternalEvents and lone s.events1:> ExternalEvents and no s.events2 :> ExternalEventsor ...
 *           no s.events0 :> ExternalEvents and no s.events1:> ExternalEvents and lone s.events2:> ExternalEvents or ...
 *  }
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

public class AddSingleEventInputFact {

	public static void addSingleEventInputFact(DashModule d) {
		if (d.hasEnvironmentalEvents()) {
			Expr e;
			Expr b = createFalse();
			for (int i=0;i <= d.getMaxDepthParams(); i++) {
				if (d.hasEventsAti(i)) {
					e = createTrue();
			    	for (int j=0;j <= d.getMaxDepthParams(); j++) {
			            if (d.hasEventsAti(j)) {
			            	if (i==j) {
			            		e = createAnd(e,createLone(createRangeRes(curEvents(i), allEnvironmentalEventsVar())));
			            	} else {
			            		e = createAnd(e,createNo(createRangeRes(curEvents(i), allEnvironmentalEventsVar())));
			            	}
			            }
			        }
			        b = createOr(b,e);
			    }
		    } 
		    List<Expr> body = new ArrayList<Expr>();
		    if (DashOptions.isElectrum) body.add(b);  	
		    else body.add(createAll(curDecls(),b));  	
			d.alloyString += d.addFactSimple(DashStrings.singleEventName, body);
		}
	}
}
