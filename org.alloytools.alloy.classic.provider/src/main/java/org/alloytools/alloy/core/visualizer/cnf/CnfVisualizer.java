package org.alloytools.alloy.core.visualizer.cnf;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.core.visualizer.BaseVisualizer;
import org.alloytools.alloy.infrastructure.api.AlloyVisualizer;

@AlloyVisualizer(
                 name = "cnf" )
public class CnfVisualizer extends BaseVisualizer implements Visualizer {



    public CnfVisualizer(Alloy alloy) {
        super(alloy, CnfSolutionToStringRenderer.class);
    }

    @Override
    public String getName() {
        return "cnf";
    }

    @Override
    public String getDescription() {
        return "Displays the cnf of kodkod plugins";
    }

}
