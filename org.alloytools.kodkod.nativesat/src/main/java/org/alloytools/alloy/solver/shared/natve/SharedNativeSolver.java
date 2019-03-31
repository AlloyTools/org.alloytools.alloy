package org.alloytools.alloy.solver.shared.natve;

import kodkod.engine.satlab.NativeSolver;

public abstract class SharedNativeSolver extends NativeSolver {

    protected SharedNativeSolver(long peer) {
        super(peer);
    }

}
