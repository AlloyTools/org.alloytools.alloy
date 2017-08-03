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

public final class TestSlow {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/A");
        Relation x7 = Relation.unary("this/Relation");
        Relation x8 = Relation.nary("this/Relation.r", 5);

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0",
                "1", "2", "3", "4", "5", "6", "7", "unused0", "unused1");

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
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("unused0"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("unused1"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(5);
        x8_upper.add(factory.tuple("unused1").product(factory.tuple("unused0")).product(
                factory.tuple("unused0")).product(factory.tuple("unused0")).product(
                factory.tuple("unused0")));
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
        Expression x19 = x6.product(x6);
        Expression x18 = x6.product(x19);
        Expression x17 = x6.product(x18);
        Formula x15 = x16.in(x17);
        Variable x22 = Variable.unary("x22");
        Decls x21 = x22.oneOf(x6);
        Expression x26 = x22.join(x16);
        Expression x28 = x6.product(x6);
        Expression x27 = x6.product(x28);
        Formula x25 = x26.in(x27);
        Variable x31 = Variable.unary("x31");
        Decls x30 = x31.oneOf(x6);
        Expression x35 = x31.join(x26);
        Expression x36 = x6.product(x6);
        Formula x34 = x35.in(x36);
        Variable x39 = Variable.unary("x39");
        Decls x38 = x39.oneOf(x6);
        Expression x42 = x39.join(x35);
        Formula x41 = x42.one();
        Formula x43 = x42.in(x6);
        Formula x40 = x41.and(x43);
        Formula x37 = x40.forAll(x38);
        Formula x33 = x34.and(x37);
        Variable x46 = Variable.unary("x46");
        Decls x45 = x46.oneOf(x6);
        Expression x48 = x35.join(x46);
        Formula x47 = x48.in(x6);
        Formula x44 = x47.forAll(x45);
        Formula x32 = x33.and(x44);
        Formula x29 = x32.forAll(x30);
        Formula x24 = x25.and(x29);
        Variable x52 = Variable.unary("x52");
        Decls x51 = x52.oneOf(x6);
        Variable x55 = Variable.unary("x55");
        Decls x54 = x55.oneOf(x6);
        Decls x50 = x51.and(x54);
        Expression x60 = x52.product(x55);
        Expression x61 = x6.product(x6);
        Formula x59 = x60.in(x61);
        Variable x64 = Variable.unary("x64");
        Decls x63 = x64.oneOf(x6);
        Expression x67 = x64.join(x60);
        Formula x66 = x67.one();
        Formula x68 = x67.in(x6);
        Formula x65 = x66.and(x68);
        Formula x62 = x65.forAll(x63);
        Formula x58 = x59.and(x62);
        Variable x71 = Variable.unary("x71");
        Decls x70 = x71.oneOf(x6);
        Expression x73 = x60.join(x71);
        Formula x72 = x73.in(x6);
        Formula x69 = x72.forAll(x70);
        Formula x57 = x58.and(x69);
        Expression x76 = x26.join(x55);
        Expression x75 = x76.join(x52);
        Formula x74 = x75.in(x6);
        Formula x56 = x57.implies(x74);
        Formula x49 = x56.forAll(x50);
        Formula x23 = x24.and(x49);
        Formula x20 = x23.forAll(x21);
        Formula x14 = x15.and(x20);
        Variable x80 = Variable.unary("x80");
        Decls x79 = x80.oneOf(x6);
        Variable x82 = Variable.unary("x82");
        Decls x81 = x82.oneOf(x6);
        Variable x84 = Variable.unary("x84");
        Decls x83 = x84.oneOf(x6);
        Decls x78 = x79.and(x81).and(x83);
        Expression x90 = x82.product(x84);
        Expression x89 = x80.product(x90);
        Expression x92 = x6.product(x6);
        Expression x91 = x6.product(x92);
        Formula x88 = x89.in(x91);
        Variable x95 = Variable.unary("x95");
        Decls x94 = x95.oneOf(x6);
        Expression x99 = x95.join(x89);
        Expression x100 = x6.product(x6);
        Formula x98 = x99.in(x100);
        Variable x103 = Variable.unary("x103");
        Decls x102 = x103.oneOf(x6);
        Expression x106 = x103.join(x99);
        Formula x105 = x106.one();
        Formula x107 = x106.in(x6);
        Formula x104 = x105.and(x107);
        Formula x101 = x104.forAll(x102);
        Formula x97 = x98.and(x101);
        Variable x110 = Variable.unary("x110");
        Decls x109 = x110.oneOf(x6);
        Expression x112 = x99.join(x110);
        Formula x111 = x112.in(x6);
        Formula x108 = x111.forAll(x109);
        Formula x96 = x97.and(x108);
        Formula x93 = x96.forAll(x94);
        Formula x87 = x88.and(x93);
        Variable x116 = Variable.unary("x116");
        Decls x115 = x116.oneOf(x6);
        Variable x118 = Variable.unary("x118");
        Decls x117 = x118.oneOf(x6);
        Decls x114 = x115.and(x117);
        Expression x123 = x116.product(x118);
        Expression x124 = x6.product(x6);
        Formula x122 = x123.in(x124);
        Variable x127 = Variable.unary("x127");
        Decls x126 = x127.oneOf(x6);
        Expression x130 = x127.join(x123);
        Formula x129 = x130.one();
        Formula x131 = x130.in(x6);
        Formula x128 = x129.and(x131);
        Formula x125 = x128.forAll(x126);
        Formula x121 = x122.and(x125);
        Variable x134 = Variable.unary("x134");
        Decls x133 = x134.oneOf(x6);
        Expression x136 = x123.join(x134);
        Formula x135 = x136.in(x6);
        Formula x132 = x135.forAll(x133);
        Formula x120 = x121.and(x132);
        Expression x139 = x89.join(x118);
        Expression x138 = x139.join(x116);
        Formula x137 = x138.in(x6);
        Formula x119 = x120.implies(x137);
        Formula x113 = x119.forAll(x114);
        Formula x86 = x87.and(x113);
        Expression x143 = x16.join(x84);
        Expression x142 = x143.join(x82);
        Expression x141 = x142.join(x80);
        Formula x140 = x141.in(x6);
        Formula x85 = x86.implies(x140);
        Formula x77 = x85.forAll(x78);
        Formula x13 = x14.and(x77);
        Formula x10 = x13.forAll(x11);
        Expression x148 = x8.join(Expression.UNIV);
        Expression x147 = x148.join(Expression.UNIV);
        Expression x146 = x147.join(Expression.UNIV);
        Expression x145 = x146.join(Expression.UNIV);
        Formula x144 = x145.in(x7);
        Formula x149 = x0.eq(x0);
        Formula x150 = x1.eq(x1);
        Formula x151 = x2.eq(x2);
        Formula x152 = x3.eq(x3);
        Formula x153 = x4.eq(x4);
        Formula x154 = x5.eq(x5);
        Formula x155 = x6.eq(x6);
        Formula x156 = x7.eq(x7);
        Formula x157 = x8.eq(x8);
        Formula x9 = Formula.compose(FormulaOperator.AND, x10, x144, x149, x150, x151, x152, x153,
                x154, x155, x156, x157);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        //solver.options().setFlatten(false);
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
