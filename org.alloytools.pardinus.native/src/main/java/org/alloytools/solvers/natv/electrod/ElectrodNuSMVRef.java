package org.alloytools.solvers.natv.electrod;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class ElectrodNuSMVRef extends ElectrodRef {

    private static final long serialVersionUID = 1L;


    public ElectrodNuSMVRef() {
        super("NuSMV");
    }

    @Override
    public String id() {
        return "electrod.nusmv";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("`nuSMV` is a reimplementation and extension of `SMV`, the original Symbolic Model Verifier developed at Carnegie Mellon University. It is a software tool for the formal verification of finite state systems, which can be used to check specifications of hardware and software systems. `nuSMV` allows users to describe systems in a high-level input language and to specify properties to be verified using temporal logics such as CTL (Computation Tree Logic) and LTL (Linear Temporal Logic). The tool uses symbolic model checking techniques, including Binary Decision Diagrams (BDDs), to efficiently verify complex systems against the given specifications. It supports various analysis modes, including model checking, interactive simulation, and counterexample generation, facilitating the detection and diagnosis of design errors.");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/NuSMV combination in some way";
    }
}
