/*
 * The translation is done in place on the Dash module.
 * This is the same for Electrum and other.
 */

package ca.uwaterloo.watform.dashtoalloy;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.core.DashOptions;

public class DashToAlloy {

    public static void translate(DashModule d) {
        assert(d.hasRoot()); // there is a Dash component in this module
        AddSpaceSignatures.addSpaceSignatures(d);  // state, parameter, buffer space
        AddSnapshotSignature.addSnapshotSignature(d);
        AddInit.addInit(d);
        AddInv.addInv(d);
        for (String tfqn: d.getAllTransNames()) {
            AddTransPre.addTransPre(d,tfqn);
            AddTransPost.addTransPost(d,tfqn);
            //createTransSemantics(t);
            if (d.hasConcurrency()) AddTransIsEnabledAfterStep.addTransIsEnabledAfterStep(d,tfqn);
            AddTrans.addTrans(d,tfqn);
        }
        if (d.hasConcurrency())
            AddTestIfNextStable.addTestIfNextStable(d);

        AddSmallStep.addSmallStep(d);

        AddStutter.addStutter(d);
        AddAllSnapshotsDifferentFact.addAllSnapshotsDifferentFact(d);
        AddEnoughOperationsPred.addEnoughOperationsPred(d);
        
        if (DashOptions.isTcmc) AddCompleteBigSteps.addCompleteBigSteps(d);
        

            
        if (DashOptions.singleEventInput)
            AddSingleEventInputPred.addSingleEventInputPred(d);

        if (DashOptions.isTcmc ) {
            AddTcmc.addTcmcFact(d);
            // other methods only consider reachable snapshots so no extra
            // predicate is needed
            AddReachabilityPred.addReachabilityPred(d);
            AddTcmc.addStrongNoStutterPred(d);

        } else if (DashOptions.isTraces) {
            AddTraces.addTracesFact(d);
            AddTraces.addStrongNoStutterPred(d);

        } else if (DashOptions.isElectrum) {
            AddElectrumFact.addElectrumFact(d);
        }
    }
}

