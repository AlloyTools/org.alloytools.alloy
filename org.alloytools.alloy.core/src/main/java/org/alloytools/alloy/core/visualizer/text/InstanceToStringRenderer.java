package org.alloytools.alloy.core.visualizer.text;

import java.util.Formatter;
import java.util.Map;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IAtom.BasicType;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSignature;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.alloytools.alloy.core.visualizer.BaseRenderer;


public class InstanceToStringRenderer extends BaseRenderer<Instance,String> implements Renderer<Instance,String> {


    InstanceToStringRenderer(Alloy alloy) {
        super(alloy, TextOptions::new);
    }

    @Override
    public <T extends VisualizerOptions> String render(Instance instance, AlloyOptions< ? extends T> options) {
        return render(f -> render(f, instance, (TextOptions) options.get()));
    }


    static void render(Formatter f, Instance inst, TextOptions options) {
        for (TSignature sig : inst.getSignatures()) {
            f.format("%s\t1%s\n", sig, inst.getAtoms(sig));
        }
        f.format("\n");
        inst.getVariables().forEach((k, v) -> {
            f.format("%s\t1%s\n", k, v);
        });
        f.format("\n");
        IRelation eval = inst.eval("univ");
        for (IAtom atom : eval.asList()) {
            if (atom.getBasicType() == BasicType.OBJECT) {

                Map<TField,IRelation> object = inst.getObject(atom);
                f.format("%s\n", atom);
                object.forEach((k, v) -> {
                    f.format("  %s\t", k.getName());
                    f.format("%s\f", v);
                });
                f.format("\n");
            }
        }
    }

}
