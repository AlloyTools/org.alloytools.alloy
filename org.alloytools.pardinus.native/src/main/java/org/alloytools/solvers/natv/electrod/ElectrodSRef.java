package org.alloytools.solvers.natv.electrod;

import java.util.Optional;

import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.solvers.api.NativeCode;

public class ElectrodSRef extends SATFactory {


    private static final long serialVersionUID = 1L;

    @Override
    public String id() {
        return "electrodS";
    }


    @Override
    public boolean isPresent() {
        return NativeCode.platform.isPresentExe("electrod") && NativeCode.platform.isPresentExe("nuXmv") && super.isPresent();
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod", "NuSmv"
        };
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.of("uSMV is a symbolic model checker, a tool that can automatically check properties of finite-state systems. The name stands for \"New Symbolic Model Verifier.\" It was developed as a joint project between FBK-IRST (Fondazione Bruno Kessler - Istituto per la Ricerca Scientifica e Tecnologica) and Carnegie Mellon University (CMU).\n" + "NuSMV aims to verify whether a given system model, specified in a formal language, satisfies certain properties. These properties are typically specified in temporal logic, which allows reasoning about sequences of states over time.");
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
        return new ExternalSolver("electrod", null, true, "-t", "NuSmv");
    }

    @Override
    public String type() {
        return "external";
    }


}
