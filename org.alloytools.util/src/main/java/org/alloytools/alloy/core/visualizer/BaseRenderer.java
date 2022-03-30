package org.alloytools.alloy.core.visualizer;

import java.util.Formatter;
import java.util.function.Consumer;
import java.util.function.Supplier;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.justif.util.Justif;

public abstract class BaseRenderer<A, O> implements Renderer<A,O> {

    protected final Alloy                        alloy;
    final Supplier< ? extends VisualizerOptions> newOptions;

    protected BaseRenderer(Alloy alloy, Supplier< ? extends VisualizerOptions> optionsType) {
        this.alloy = alloy;
        this.newOptions = optionsType;
    }

    @SuppressWarnings("unchecked" )
    @Override
    public <T extends VisualizerOptions> AlloyOptions<T> newOptions() {
        return (AlloyOptions<T>) alloy.asOptions(newOptions.get());
    }


    protected String render(Consumer<Formatter> cons) {
        Justif f = new Justif(120, 0, 40, 60, 80, 100);
        cons.accept(f.formatter());
        return f.wrap();
    }

}
