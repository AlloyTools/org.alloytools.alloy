/*
 * 
 * In a weird case where a transition is triggered on an internal event
 * but its guard depends on an external var value
 * it won't be triggered after a stutter
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

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

import static ca.uwaterloo.watform.dashtoalloy.Common.*;

public class AddStutter {

	// low priority no environmental stutter predicate

	public static void addStutter(DashModule d) {

        
        List<Expr> body = new ArrayList<Expr>();
        
        // all the dsh defined parts of the snapshot stay the same
        if (d.hasConcurrency()) body.add(noChange(DashStrings.stableName));
        for (int i = 0; i <= d.getMaxDepthParams(); i++) {
                if (!d.hasOnlyOneState())
                	body.add(noChange(DashStrings.confName+Integer.toString(i)));
        	if (d.hasConcurrency()) 
                        body.add(noChange(DashStrings.scopesUsedName+Integer.toString(i)));
                if (i == 0) 
                        body.add(createEquals(nextTransTaken(i), createVar(DashStrings.noTransName)));
        	else 
                        body.add(createEquals(nextTransTaken(i), createNoneArrow(i)));
                if (d.hasEvents() && d.hasInternalEventsAti(i))
        		// internal events go away
        		// external events can be added
 				body.add(createEquals(
                                    createRangeRes(nextEvents(i),allInternalEventsVar()), 
                                    createNoneArrow(i)));
        }

        // internal vars
        // stays the same for all parameter values
        // so can just say that the whole relation is the same and no parameter values needed !!
        for (String vfqn: d.getAllInternalVarNames()) body.add(noChange(vfqn));
        // buffers are all internal
       	for (String bfqn: d.getAllBufferNames()) body.add(noChange(bfqn));
        d.alloyString += d.addPredSimple(DashStrings.stutterName, curNextDecls(), body);

    }

    private static Expr noChange(String n) {
    	return createEquals(nextJoinExpr(createVar(translateFQN(n))), curJoinExpr(createVar(translateFQN(n))));
    }
}

