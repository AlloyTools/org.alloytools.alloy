package org.alloytools.alloy.core.visualizer.text;

import java.util.Formatter;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.TOpen;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.core.visualizer.BaseRenderer;

public class ModuleToStringRenderer extends BaseRenderer<TModule,String> implements Renderer<TModule,String> {

    public ModuleToStringRenderer(Alloy alloy) {
        super(alloy, TextOptions::new);
    }

    @Override
    public <T extends VisualizerOptions> String render(TModule module, AlloyOptions< ? extends T> options) {
        return render(f -> renderSummary(f, module, (TextOptions) options.get()));
    }


    static void renderSummary(Formatter f, TModule module, TextOptions options) {
        f.format("paths\t");
        renderChildren(f, module, options, "");
        f.format("\n");
        f.format("compiler\t%s\n", module.getCompiler());
        f.format("sigs\t%s\n", module.getSignatures().values());
        if (!module.getErrors().isEmpty()) {
            f.format("errors\t");

            for (CompilerMessage msg : module.getErrors()) {
                f.format("%s\f", msg.getMessage());
            }
            f.format("\n");
        }
        if (!module.getWarnings().isEmpty()) {
            f.format("warnings\t");

            for (CompilerMessage msg : module.getWarnings()) {
                f.format("%s\f", msg.getMessage());
            }
            f.format("\n");
        }
    }

    private static void renderChildren(Formatter f, TModule m, TextOptions options, String indent) {
        f.format("%s%s\f", indent, m.getPath().orElse("anonymous"));
        for (TOpen o : m.getOpens()) {
            renderChildren(f, o.getModule(), options, indent + "\u00A0");
        }
    }
}
