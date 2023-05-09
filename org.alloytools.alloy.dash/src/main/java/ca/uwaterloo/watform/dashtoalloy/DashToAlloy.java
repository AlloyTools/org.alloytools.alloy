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
        AddSpaceSignatures.addSpaceSignatures(d);  // state, transition, parameter, buffer space
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

        if (DashOptions.isTraces)
            AddTracesFact.addTracesFact(d);
        else if (DashOptions.isTcmc)
            AddTcmcFact.addTcmcFact(d);
        else if (DashOptions.isElectrum)
            AddElectrumFact.addElectrumFact(d);
    }
}

