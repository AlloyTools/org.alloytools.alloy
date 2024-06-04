package edu.mit.csail.sdg.alloy4;

import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.getopt.Options;

@AlloyMain
public class WorkerEngineFacade {


    public void __worker(Options options) {
        WorkerEngine.main(options._arguments().toArray(String[]::new));
    }

    @Override
    public String toString() {
        return "WorkerEngine";
    }
}
