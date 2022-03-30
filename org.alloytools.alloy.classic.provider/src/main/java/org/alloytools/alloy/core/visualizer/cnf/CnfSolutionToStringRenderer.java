package org.alloytools.alloy.core.visualizer.cnf;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.core.visualizer.BaseRenderer;

import kodkod.engine.satlab.TransientPlugin;


public class CnfSolutionToStringRenderer extends BaseRenderer<Solution,String> implements Renderer<Solution,String> {

    static class CnfOptions extends VisualizerOptions {
    }

    public CnfSolutionToStringRenderer(Alloy alloy) {
        super(alloy, CnfOptions::new);
    }

    @Override
    public <T extends VisualizerOptions> String render(Solution instance, AlloyOptions< ? extends T> options) {
        WriteCNF w = new WriteCNF();
        TransientPlugin tp = new TransientPlugin(alloy, w);
        tp.solve(instance.getCommand(), null);
        return w.getBuffer().toString();
    }

}
