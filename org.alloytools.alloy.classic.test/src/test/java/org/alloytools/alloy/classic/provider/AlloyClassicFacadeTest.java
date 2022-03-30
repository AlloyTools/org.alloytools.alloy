package org.alloytools.alloy.classic.provider;


import static org.assertj.core.api.Assertions.assertThat;

import java.util.Optional;

import org.alloytools.alloy.core.api.Alloy;
import org.alloytools.alloy.core.api.AlloyOptions;
import org.alloytools.alloy.core.api.Solution;
import org.alloytools.alloy.core.api.Visualizer.Renderer;
import org.alloytools.alloy.core.api.VisualizerOptions;
import org.junit.Test;


public class AlloyClassicFacadeTest {

    @Test
    public void testVisualizers() {
        Alloy acf = new AlloyClassicFacade();

        assertThat(acf.getVisualizers()).isNotEmpty();
        System.out.println(acf.getVisualizers());

        Optional<Renderer<Solution,String>> r = acf.findRenderer("text", Solution.class, String.class);
        assertThat(r).isPresent();

        Solution solution = acf.getSolution("sig Foo {} run { some Foo } for 2");

        Renderer<Solution,String> renderer = r.get();
        AlloyOptions<VisualizerOptions> opts = renderer.newOptions();
        opts.set("maxConfigurations", 3);
        opts.set("pedigree", true);

        String render = r.get().render(solution, opts);
        assertThat(render).isNotNull();
        System.out.println(render);
    }


    @Test
    public void testVisualizers2() {
        Alloy acf = new AlloyClassicFacade();

        assertThat(acf.getVisualizers()).isNotEmpty();
        System.out.println(acf.getVisualizers());

        Optional<Renderer<Solution,String>> r = acf.findRenderer("text", Solution.class, String.class);
        assertThat(r).isPresent();

        Solution solution = acf.getSolution("sig Foo { var n : Int ->Int } { one n } run { some f : Foo | f.n != f.n'} for 2");

        Renderer<Solution,String> renderer = r.get();
        AlloyOptions<VisualizerOptions> opts = renderer.newOptions();
        opts.set("maxConfigurations", 3);
        opts.set("pedigree", true);

        String render = r.get().render(solution, opts);
        assertThat(render).isNotNull();
        System.out.println(render);
    }

    @Test
    public void testCnf() {
        Alloy acf = new AlloyClassicFacade();
        Renderer<Solution,String> r = acf.findRenderer("cnf", Solution.class, String.class).get();
        Solution solution = acf.getSolution("sig Foo { var n : Int ->Int } { one n } run { some f : Foo | f.n != f.n'} for 2");
        String output = r.render(solution);
        System.out.println(output);
    }
}
