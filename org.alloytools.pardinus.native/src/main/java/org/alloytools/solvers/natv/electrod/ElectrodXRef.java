package org.alloytools.solvers.natv.electrod;

import java.util.Optional;

import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.solvers.api.NativeCode;

public class ElectrodXRef extends SATFactory {

    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "electrodX";
    }


    @Override
    public boolean isPresent() {
        return NativeCode.platform.isPresentExe("electrod") && NativeCode.platform.isPresentExe("nuXmv");
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod", "nuXmv"
        };
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("NuXmv is a symbolic model checker developed as an evolution of the NuSMV open source model checker. It was designed with the aim to provide an efficient verification platform for systems with both infinite and finite state variables, by integrating and improving on features available in NuSMV and other predecessor tools.\n" + "NuXmv allows for the verification of both safety (i.e., something bad will never happen) and liveness (i.e., something good will eventually happen) properties of transition systems. These systems can be represented as finite state machines, where properties are generally specified in temporal logic.");
    }

    @Override
    public String toString() {
        return id();
    }

    @Override
    public boolean incremental() {
        return false;
    }

    @Override
    public boolean unbounded() {
        return true;
    }


    @Override
    public SATSolver instance() {
        return new ExternalSolver("electrod", null, true, "-t", "nuXmv");
    }

    @Override
    public String type() {
        return "external";
    }

}
