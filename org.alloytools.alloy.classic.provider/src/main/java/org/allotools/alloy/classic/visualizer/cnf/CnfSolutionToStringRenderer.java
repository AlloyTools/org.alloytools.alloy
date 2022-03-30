 package org.allotools.alloy.classic.visualizer.cnf;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.core.visualizer.BaseRenderer;


public class CnfSolutionToStringRenderer extends BaseRenderer<Solution,String> {

    static class CnfOptions extends VisualizerOptions {
    }

    public CnfSolutionToStringRenderer(Alloy alloy) {
        super(alloy, CnfOptions::new);
    }

    @Override
    public <T extends VisualizerOptions> String render(Solution solution, AlloyOptions< ? extends T> options) {
        TModule module = solution.getModule();
        TCommand command = solution.getCommand();

        return null;
    }

}
