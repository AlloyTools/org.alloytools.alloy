package tests;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.Skolemizer;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.nodes.AnnotatedNode;
import kodkod.util.nodes.PrettyPrinter;

public class Tmp {


    public static void main2(String[] args) {
        Relation rVar = Relation.unary("Var");
        Relation rVal = Relation.unary("Val");
        Variable env = Variable.nary("env", 2);
        Variable v = Variable.nary("v", 1);
        Formula f = env.in(rVar.product(rVal)).and(v.join(env).one().forAll(v.oneOf(rVar)))
                .implies(Formula.TRUE)
                .forAll(env.setOf(rVar.product(rVal)));
        System.out.println(PrettyPrinter.print(f, 0));

        Universe universe = new Universe("r1", "r2", "r3", "q1", "q2");
        Bounds bounds = new Bounds(universe);
        bounds.bound(rVar, universe.factory().setOf("r1", "r2", "r3"));
        bounds.bound(rVal, universe.factory().setOf("q1", "q2"));
        Options options = new Options();
        options.setSkolemDepth(0);
        AnnotatedNode<Formula> anno = AnnotatedNode.annotateRoots(f);
        anno.annotateHOL();

        anno = FullNegationPropagator.toNNF(anno, options.reporter());
        System.out.println("-------------");
        System.out.println(PrettyPrinter.print(anno.node(), 0));

        Formula skol = Skolemizer.skolemize(anno, bounds, options).node();

        System.out.println("-------------");
        System.out.println(PrettyPrinter.print(skol, 0));
    }

    public static void main(String[] args) {
        Relation rNode = Relation.unary("Node");
        Relation rVar = Relation.unary("Var");
        Relation rVal = Relation.unary("Val");
        
        Variable root = Variable.unary("root");
        Variable envI = Variable.nary("envI", 2);
        Variable eval = Variable.nary("eval", 2);
        
        Formula f = root.join(eval).some()//.and(envI.in(eval))
          .forSome(eval.setOf(rNode.product(rVal)))
          .forAll(envI.setOf(rVar.product(rVal)))
          .forSome(root.oneOf(rNode));
        
        System.out.println(PrettyPrinter.print(f, 0));

        Universe universe = new Universe("i1", "i2", "i3", "n1", "n2", "v1", "v2");
        Bounds bounds = new Bounds(universe);
        TupleFactory factory = universe.factory();
        bounds.bound(rNode, factory.setOf("i1", "i2", "i3", "n1", "n2"));
        bounds.bound(rVar, factory.setOf("i1", "i2", "i3"));
        bounds.bound(rVal, factory.setOf("v1", "v2"));
        
        Options options = new Options();
        options.setSkolemDepth(1);
        AnnotatedNode<Formula> anno = AnnotatedNode.annotateRoots(f);
        Formula skol = Skolemizer.skolemize(anno, bounds, options).node();

        System.out.println("-------------");
        System.out.println(PrettyPrinter.print(skol, 0));
    }

}
