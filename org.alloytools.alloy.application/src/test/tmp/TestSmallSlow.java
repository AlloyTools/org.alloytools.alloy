package tmp;
import java.util.Arrays;
import java.util.List;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.util.nodes.PrettyPrinter;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.Options;

public final class TestSmallSlow {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/A");
        Relation x7 = Relation.unary("this/Relation");
        Relation x8 = Relation.nary("this/Relation.r", 4);

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0",
                "1", "2", "3", "4", "5", "6", "7", "A$0", "A$1", "A$2", "Relation$0", "unused0",
                "unused1");

        Universe universe = new Universe(atomlist);
        TupleFactory factory = universe.factory();
        Bounds bounds = new Bounds(universe);

        TupleSet x0_upper = factory.noneOf(1);
        x0_upper.add(factory.tuple("-8"));
        bounds.boundExactly(x0, x0_upper);

        TupleSet x1_upper = factory.noneOf(1);
        x1_upper.add(factory.tuple("0"));
        bounds.boundExactly(x1, x1_upper);

        TupleSet x2_upper = factory.noneOf(1);
        x2_upper.add(factory.tuple("7"));
        bounds.boundExactly(x2, x2_upper);

        TupleSet x3_upper = factory.noneOf(2);
        x3_upper.add(factory.tuple("-8").product(factory.tuple("-7")));
        x3_upper.add(factory.tuple("-7").product(factory.tuple("-6")));
        x3_upper.add(factory.tuple("-6").product(factory.tuple("-5")));
        x3_upper.add(factory.tuple("-5").product(factory.tuple("-4")));
        x3_upper.add(factory.tuple("-4").product(factory.tuple("-3")));
        x3_upper.add(factory.tuple("-3").product(factory.tuple("-2")));
        x3_upper.add(factory.tuple("-2").product(factory.tuple("-1")));
        x3_upper.add(factory.tuple("-1").product(factory.tuple("0")));
        x3_upper.add(factory.tuple("0").product(factory.tuple("1")));
        x3_upper.add(factory.tuple("1").product(factory.tuple("2")));
        x3_upper.add(factory.tuple("2").product(factory.tuple("3")));
        x3_upper.add(factory.tuple("3").product(factory.tuple("4")));
        x3_upper.add(factory.tuple("4").product(factory.tuple("5")));
        x3_upper.add(factory.tuple("5").product(factory.tuple("6")));
        x3_upper.add(factory.tuple("6").product(factory.tuple("7")));
        bounds.boundExactly(x3, x3_upper);

        TupleSet x4_upper = factory.noneOf(1);
        x4_upper.add(factory.tuple("0"));
        x4_upper.add(factory.tuple("1"));
        x4_upper.add(factory.tuple("2"));
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("A$0"));
        x6_upper.add(factory.tuple("A$1"));
        x6_upper.add(factory.tuple("A$2"));
        bounds.boundExactly(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("unused0"));
        x7_upper.add(factory.tuple("unused1"));
        x7_upper.add(factory.tuple("Relation$0"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(4);
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$0").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        bounds.bound(x8, x8_upper);

        bounds.boundExactly(-8, factory.range(factory.tuple("-8"), factory.tuple("-8")));
        bounds.boundExactly(-7, factory.range(factory.tuple("-7"), factory.tuple("-7")));
        bounds.boundExactly(-6, factory.range(factory.tuple("-6"), factory.tuple("-6")));
        bounds.boundExactly(-5, factory.range(factory.tuple("-5"), factory.tuple("-5")));
        bounds.boundExactly(-4, factory.range(factory.tuple("-4"), factory.tuple("-4")));
        bounds.boundExactly(-3, factory.range(factory.tuple("-3"), factory.tuple("-3")));
        bounds.boundExactly(-2, factory.range(factory.tuple("-2"), factory.tuple("-2")));
        bounds.boundExactly(-1, factory.range(factory.tuple("-1"), factory.tuple("-1")));
        bounds.boundExactly(0, factory.range(factory.tuple("0"), factory.tuple("0")));
        bounds.boundExactly(1, factory.range(factory.tuple("1"), factory.tuple("1")));
        bounds.boundExactly(2, factory.range(factory.tuple("2"), factory.tuple("2")));
        bounds.boundExactly(3, factory.range(factory.tuple("3"), factory.tuple("3")));
        bounds.boundExactly(4, factory.range(factory.tuple("4"), factory.tuple("4")));
        bounds.boundExactly(5, factory.range(factory.tuple("5"), factory.tuple("5")));
        bounds.boundExactly(6, factory.range(factory.tuple("6"), factory.tuple("6")));
        bounds.boundExactly(7, factory.range(factory.tuple("7"), factory.tuple("7")));

        Variable x12 = Variable.unary("this");
        Decls x11 = x12.oneOf(x7);
        Expression x16 = x12.join(x8);
        Expression x18 = x6.product(x6);
        Expression x17 = x6.product(x18);
        Formula x15 = x16.in(x17);
        Variable x21 = Variable.unary("x21");
        Decls x20 = x21.oneOf(x6);
        Expression x25 = x21.join(x16);
        Expression x26 = x6.product(x6);
        Formula x24 = x25.in(x26);
        Variable x29 = Variable.unary("x29");
        Decls x28 = x29.oneOf(x6);
        Expression x32 = x29.join(x25);
        Formula x31 = x32.one();
        Formula x33 = x32.in(x6);
        Formula x30 = x31.and(x33);
        Formula x27 = x30.forAll(x28);
        Formula x23 = x24.and(x27);
        Variable x36 = Variable.unary("x36");
        Decls x35 = x36.oneOf(x6);
        Expression x38 = x25.join(x36);
        Formula x37 = x38.in(x6);
        Formula x34 = x37.forAll(x35);
        Formula x22 = x23.and(x34);
        Formula x19 = x22.forAll(x20);
        Formula x14 = x15.and(x19);
        Variable x42 = Variable.unary("x42");
        Decls x41 = x42.oneOf(Expression.UNIV);
        Variable x45 = Variable.unary("x45");
        Decls x44 = x45.oneOf(Expression.UNIV);
        Decls x40 = x41.and(x44);
        Expression x50 = x42.product(x45);
        Expression x51 = x6.product(x6);
        Formula x49 = x50.in(x51);
        Variable x54 = Variable.unary("x54");
        Decls x53 = x54.oneOf(x6);
        Expression x57 = x54.join(x50);
        Formula x56 = x57.one();
        Formula x58 = x57.in(x6);
        Formula x55 = x56.and(x58);
        Formula x52 = x55.forAll(x53);
        Formula x48 = x49.and(x52);
        Variable x61 = Variable.unary("x61");
        Decls x60 = x61.oneOf(x6);
        Expression x63 = x50.join(x61);
        Formula x62 = x63.in(x6);
        Formula x59 = x62.forAll(x60);
        Formula x47 = x48.and(x59);
        Expression x66 = x16.join(x45);
        Expression x65 = x66.join(x42);
        Formula x64 = x65.in(x6);
        Formula x46 = x47.implies(x64);
        Formula x39 = x46.forAll(x40);
        Formula x13 = x14.and(x39);
        Formula x10 = x13.forAll(x11);
        Expression x70 = x8.join(Expression.UNIV);
        Expression x69 = x70.join(Expression.UNIV);
        Expression x68 = x69.join(Expression.UNIV);
        Formula x67 = x68.in(x7);
        Formula x71 = x0.eq(x0);
        Formula x72 = x1.eq(x1);
        Formula x73 = x2.eq(x2);
        Formula x74 = x3.eq(x3);
        Formula x75 = x4.eq(x4);
        Formula x76 = x5.eq(x5);
        Formula x77 = x6.eq(x6);
        Formula x78 = x7.eq(x7);
        Formula x79 = x8.eq(x8);
        Formula x9 = Formula.compose(FormulaOperator.AND, x10, x67, x71, x72, x73, x74, x75, x76,
                x77, x78, x79);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
//        solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        
        System.out.println(PrettyPrinter.print(x9, 0));
        System.out.println(bounds);
        
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x9, bounds);
        System.out.println(sol.toString());
        
        Instance inst = sol.instance();
        Evaluator ev = new Evaluator(inst);
        
        System.out.println("Universe: " + ev.evaluate(Expression.UNIV));
        Formula xx = x46.forAll(x40).forAll(x11);
        System.out.println(PrettyPrinter.print(xx, 2));
        System.out.println(ev.evaluate(xx));
        
        System.out.println(PrettyPrinter.print(x46, 4));
        
//        Variable r = Variable.unary("this");
//        Variable u1 = Variable.unary("u1");
//        Variable u2 = Variable.unary("u2");
//        
//        Formula ff = u1.product(u2).in(x6.product(x6)).forAll(u1.oneOf(Expression.UNIV).and(u2.oneOf(Expression.UNIV))).forAll(r.oneOf(x7));
//        System.out.println(PrettyPrinter.print(ff, 0));
//        System.out.println(ev.evaluate(ff));
        
    }
}
