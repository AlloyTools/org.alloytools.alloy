package org.alloytools.alloy.core.visualizer.text;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.Visualizer;
import org.alloytools.alloy.core.visualizer.BaseVisualizer;
import org.alloytools.alloy.infrastructure.api.AlloyVisualizer;

@AlloyVisualizer(
                 name = "text" )
public class TextVisualizer extends BaseVisualizer implements Visualizer {


    public TextVisualizer(Alloy alloy) {
        super(alloy, InstanceToStringRenderer.class, ModuleToStringRenderer.class, SolutionToStringRenderer.class);
    }

    @Override
    public String getName() {
        return "text";
    }

    @Override
    public String getDescription() {
        return "Provides a textual representation of solutions";
    }

}
