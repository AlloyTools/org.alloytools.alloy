package tmp;
import java.util.LinkedList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.nodes.PrettyPrinter;

public final class KK {

    public static void main(String[] args) throws Exception {

        Relation x6 = Relation.unary("R");
        int[] ints = new int[] {0, 1, 2};
        
        List<Object> atomlist = new LinkedList<Object>();
        atomlist.add("R$0"); 
        atomlist.add("R$1");
        atomlist.add("R$2");
        for (int i : ints) atomlist.add(i);
        
        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("R$0"));
        x6_upper.add(factory.tuple("R$1"));
        x6_upper.add(factory.tuple("R$2"));
        bounds.bound(x6, x6_upper);

        for (int i : ints) {
            bounds.boundExactly(i, factory.setOf(i));
        }

        Formula x11 = x6.some();
        IntExpression x5 = x6.count();
        Formula x9 = x11.implies(x5.gt(IntConstant.constant(0)));
        Formula x7 = x9.not();

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(2);
        //solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.println(PrettyPrinter.print(x7, 0));
        System.out.println(bounds);
        Solution sol = solver.solve(x7, bounds);
        System.out.println(sol.toString());
        
        Instance inst = sol.instance();
        Evaluator ev = new Evaluator(inst);
        System.out.println(ev.evaluate(x6.some()));
        System.out.println(ev.evaluate(x5));
        System.out.println(ev.evaluate(x5.gt(IntConstant.constant(0))));
        System.out.println(ev.evaluate(x6.some().implies(x5.gt(IntConstant.constant(0))).not()));
        System.out.println(ev.evaluate(x7));
        
        
    }
}
