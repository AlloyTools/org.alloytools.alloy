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

public final class TestSmallFast {

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
                "1", "2", "3", "4", "5", "6", "7", "A$0", "A$1", "A$2", "Relation$0", "Relation$1",
                "Relation$2");

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
        x7_upper.add(factory.tuple("Relation$0"));
        x7_upper.add(factory.tuple("Relation$1"));
        x7_upper.add(factory.tuple("Relation$2"));
        bounds.boundExactly(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(4);
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
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$1").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$0")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$1")).product(
                factory.tuple("A$2")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$0")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$1")).product(factory.tuple("A$2")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$0")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
                factory.tuple("A$2")).product(factory.tuple("A$1")));
        x8_upper.add(factory.tuple("Relation$2").product(factory.tuple("A$2")).product(
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
        Expression x17 = x18.product(x6);
        Formula x15 = x16.in(x17);
        Variable x22 = Variable.unary("x22");
        Decls x21 = x22.oneOf(Expression.UNIV);
        Variable x25 = Variable.unary("x25");
        Decls x24 = x25.oneOf(Expression.UNIV);
        Decls x20 = x21.and(x24);
        Expression x28 = x25.product(x22);
        Expression x29 = x6.product(x6);
        Formula x27 = x28.in(x29);
        Expression x33 = x25.join(x16);
        Expression x32 = x22.join(x33);
        Formula x31 = x32.one();
        Formula x34 = x32.in(x6);
        Formula x30 = x31.and(x34);
        Formula x26 = x27.implies(x30);
        Formula x19 = x26.forAll(x20);
        Formula x14 = x15.and(x19);
        Variable x37 = Variable.unary("x37");
        Decls x36 = x37.oneOf(x6);
        Expression x39 = x16.join(x37);
        Expression x40 = x6.product(x6);
        Formula x38 = x39.in(x40);
        Formula x35 = x38.forAll(x36);
        Formula x13 = x14.and(x35);
        Formula x10 = x13.forAll(x11);
        Expression x44 = x8.join(Expression.UNIV);
        Expression x43 = x44.join(Expression.UNIV);
        Expression x42 = x43.join(Expression.UNIV);
        Formula x41 = x42.in(x7);
        Formula x45 = x0.eq(x0);
        Formula x46 = x1.eq(x1);
        Formula x47 = x2.eq(x2);
        Formula x48 = x3.eq(x3);
        Formula x49 = x4.eq(x4);
        Formula x50 = x5.eq(x5);
        Formula x51 = x6.eq(x6);
        Formula x52 = x7.eq(x7);
        Formula x53 = x8.eq(x8);
        Formula x9 = Formula.compose(FormulaOperator.AND, x10, x41, x45, x46, x47, x48, x49, x50,
                x51, x52, x53);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
//        solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        
        System.out.println(PrettyPrinter.print(x9, 0));
        
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x9, bounds);
        System.out.println(sol.toString());
    }
}
