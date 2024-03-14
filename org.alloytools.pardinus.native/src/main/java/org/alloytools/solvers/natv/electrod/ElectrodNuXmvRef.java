package org.alloytools.solvers.natv.electrod;

import java.util.Optional;

import aQute.bnd.annotation.spi.ServiceProvider;
import kodkod.engine.satlab.SATFactory;

@ServiceProvider(SATFactory.class )
public class ElectrodNuXmvRef extends ElectrodRef {

    private static final long serialVersionUID = 1L;


    public ElectrodNuXmvRef() {
        super("nuXmv");
    }

    @Override
    public String id() {
        return "electrod.nuxmv";
    }


    @Override
    public Optional<String> getDescription() {
        return Optional.of("nuXmv is a symbolic model checker for formal verification of finite state and infinite state systems. It extends and replaces the nuSMV tool, inheriting its features while introducing new functionalities and improvements. nuXmv can analyze both hardware designs and software specifications, supporting temporal logics like CTL (Computation Tree Logic) and LTL (Linear Temporal Logic) for specification of properties. It employs advanced techniques such as SAT-based and BDD-based symbolic model checking, making it effective for verifying complex systems.");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/nuXmv combination in some way";
    }

}
