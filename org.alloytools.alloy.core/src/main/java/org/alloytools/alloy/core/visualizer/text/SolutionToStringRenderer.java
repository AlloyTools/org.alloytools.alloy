package org.alloytools.alloy.core.visualizer.text;

import java.util.Formatter;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Solution.Trace;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.core.visualizer.BaseRenderer;
import org.alloytools.justif.util.Justif;


public class SolutionToStringRenderer extends BaseRenderer<Solution,String> implements Renderer<Solution,String> {

    public SolutionToStringRenderer(Alloy alloy) {
        super(alloy, TextOptions::new);
    }


    @Override
    public <T extends VisualizerOptions> String render(Solution instance, AlloyOptions< ? extends T> options) {
        Justif f = new Justif(120, 0, 40, 60, 80, 100);
        render(f.formatter(), instance, (TextOptions) options.get());
        return f.wrap();
    }


    static void render(Formatter f, Solution a, TextOptions options) {

        if (options.pedigree) {
            f.format("## SOLUTION\n");
            ModuleToStringRenderer.renderSummary(f, a.getModule(), options);
            f.format("\n");
        }

        if (!a.isSatisfied()) {
            f.format("Not satisfied\n");
            return;
        }

        if (options.maxConfigurations <= 0) {
            f.format("Satisfied\n");
            return;
        }


        int n = 0;

        config: for (Instance inst : a) {

            f.format("## INSTANCE %d\n", n);
            if (a.hasVariables()) {
                int trace = 0;
                trace: for (Trace state : a.trace(inst)) {
                    f.format("### TRACE %d\n", trace++);
                    render(f, state, options);

                    if (trace >= options.maxTraces)
                        break trace;
                }
            } else {
                InstanceToStringRenderer.render(f, inst, options);
            }

            if (++n >= options.maxConfigurations)
                break config;
        }

    }

    public static void render(Formatter f, Trace trace, TextOptions options) {
        for (int state = 0; state < trace.instances().length; state++) {
            f.format("#### STATE %d of %d\n", state, trace.instances().length);
            if (state == trace.loop()) {
                f.format(">> loop back\n", state);
            }
            InstanceToStringRenderer.render(f, trace.instances()[state], options);
        }
    }
}
