package tmp;
import java.util.Arrays;
import java.util.List;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.Options;

public final class Ok {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/A");
        Relation x7 = Relation.unary("this/B");
        Relation x8 = Relation.unary("this/Relation1");
        Relation x9 = Relation.unary("this/Relation2");
        Relation x10 = Relation.unary("this/Relation3");
        Relation x11 = Relation.unary("this/Relation4");
        Relation x12 = Relation.nary("this/Relation1.r", 3);
        Relation x13 = Relation.nary("this/Relation2.r", 3);
        Relation x14 = Relation.nary("this/Relation3.r", 3);
        Relation x15 = Relation.nary("this/Relation4.r", 3);

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0",
                "1", "2", "3", "4", "5", "6", "7", "A$0", "B$0", "Relation1$0", "Relation2$0",
                "Relation3$0", "Relation4$0");

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
        x6_upper.add(factory.tuple("A$0"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("B$0"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("Relation1$0"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("Relation2$0"));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(1);
        x10_upper.add(factory.tuple("Relation3$0"));
        bounds.bound(x10, x10_upper);

        TupleSet x11_upper = factory.noneOf(1);
        x11_upper.add(factory.tuple("Relation4$0"));
        bounds.bound(x11, x11_upper);

        TupleSet x12_upper = factory.noneOf(3);
        x12_upper.add(factory.tuple("Relation1$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")));
        x12_upper.add(factory.tuple("Relation1$0").product(factory.tuple("A$0")).product(
                factory.tuple("B$0")));
        x12_upper.add(factory.tuple("Relation1$0").product(factory.tuple("B$0")).product(
                factory.tuple("A$0")));
        x12_upper.add(factory.tuple("Relation1$0").product(factory.tuple("B$0")).product(
                factory.tuple("B$0")));
        bounds.bound(x12, x12_upper);

        TupleSet x13_upper = factory.noneOf(3);
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("A$0")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("B$0")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-8")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-7")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-6")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-5")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-4")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-3")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-2")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("-1")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("0")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("1")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("2")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("3")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("4")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("5")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("6")).product(
                factory.tuple("7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("A$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("B$0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-8")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-7")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("-1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("0")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("1")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("2")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("3")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("4")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("5")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("6")));
        x13_upper.add(factory.tuple("Relation2$0").product(factory.tuple("7")).product(
                factory.tuple("7")));
        bounds.bound(x13, x13_upper);

        TupleSet x14_upper = factory.noneOf(3);
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("A$0")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("B$0")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-8")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-7")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-6")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-5")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-4")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-3")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-2")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("-1")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("0")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("1")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("2")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("3")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("4")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("5")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("6")).product(
                factory.tuple("7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("A$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("B$0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-8")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-7")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("-1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("0")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("1")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("2")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("3")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("4")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("5")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("6")));
        x14_upper.add(factory.tuple("Relation3$0").product(factory.tuple("7")).product(
                factory.tuple("7")));
        bounds.bound(x14, x14_upper);

        TupleSet x15_upper = factory.noneOf(3);
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("A$0")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("B$0")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-8")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-7")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-6")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-5")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-4")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-3")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-2")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("-1")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("0")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("1")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("2")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("3")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("4")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("5")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("6")).product(
                factory.tuple("7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("A$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("B$0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-8")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-7")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("-1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("0")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("1")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("2")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("3")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("4")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("5")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("6")));
        x15_upper.add(factory.tuple("Relation4$0").product(factory.tuple("7")).product(
                factory.tuple("7")));
        bounds.bound(x15, x15_upper);

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

        Variable x19 = Variable.unary("p1_this");
        Decls x18 = x19.oneOf(x8);
        Expression x23 = x19.join(x12);
        Expression x25 = x6.union(x7);
        Expression x26 = x6.union(x7);
        Expression x24 = x25.product(x26);
        Formula x22 = x23.in(x24);
        Variable x29 = Variable.unary("v60");
        Decls x28 = x29.oneOf(x25);
        Expression x32 = x29.join(x23);
        Formula x31 = x32.one();
        Expression x34 = x6.union(x7);
        Formula x33 = x32.in(x34);
        Formula x30 = x31.and(x33);
        Formula x27 = x30.forAll(x28);
        Formula x21 = x22.and(x27);
        Variable x37 = Variable.unary("v61");
        Decls x36 = x37.oneOf(x26);
        Expression x39 = x23.join(x37);
        Expression x40 = x6.union(x7);
        Formula x38 = x39.in(x40);
        Formula x35 = x38.forAll(x36);
        Formula x20 = x21.and(x35);
        Formula x17 = x20.forAll(x18);
        Expression x43 = x12.join(Expression.UNIV);
        Expression x42 = x43.join(Expression.UNIV);
        Formula x41 = x42.in(x8);
        Variable x47 = Variable.unary("p1_this");
        Decls x46 = x47.oneOf(x9);
        Expression x51 = x47.join(x13);
        Expression x54 = x6.union(x7);
        Expression x53 = x54.union(Expression.INTS);
        Expression x57 = x6.union(x7);
        Expression x56 = x57.union(Expression.INTS);
        Expression x52 = x53.product(x56);
        Formula x50 = x51.in(x52);
        Variable x60 = Variable.unary("v62");
        Decls x59 = x60.oneOf(x53);
        Expression x62 = x60.join(x51);
        Expression x64 = x6.union(x7);
        Expression x63 = x64.union(Expression.INTS);
        Formula x61 = x62.in(x63);
        Formula x58 = x61.forAll(x59);
        Formula x49 = x50.and(x58);
        Variable x67 = Variable.unary("v63");
        Decls x66 = x67.oneOf(x56);
        Expression x70 = x51.join(x67);
        Formula x69 = x70.one();
        Expression x73 = x6.union(x7);
        Expression x72 = x73.union(Expression.INTS);
        Formula x71 = x70.in(x72);
        Formula x68 = x69.and(x71);
        Formula x65 = x68.forAll(x66);
        Formula x48 = x49.and(x65);
        Formula x45 = x48.forAll(x46);
        Expression x76 = x13.join(Expression.UNIV);
        Expression x75 = x76.join(Expression.UNIV);
        Formula x74 = x75.in(x9);
        Variable x79 = Variable.unary("p1_this");
        Decls x78 = x79.oneOf(x10);
        Expression x83 = x79.join(x14);
        Expression x86 = x6.union(x7);
        Expression x85 = x86.union(Expression.INTS);
        Expression x88 = x6.union(x7);
        Expression x87 = x88.union(Expression.INTS);
        Expression x84 = x85.product(x87);
        Formula x82 = x83.in(x84);
        Variable x91 = Variable.unary("v64");
        Decls x90 = x91.oneOf(x85);
        Expression x94 = x91.join(x83);
        Formula x93 = x94.one();
        Expression x97 = x6.union(x7);
        Expression x96 = x97.union(Expression.INTS);
        Formula x95 = x94.in(x96);
        Formula x92 = x93.and(x95);
        Formula x89 = x92.forAll(x90);
        Formula x81 = x82.and(x89);
        Variable x100 = Variable.unary("v65");
        Decls x99 = x100.oneOf(x87);
        Expression x103 = x83.join(x100);
        Formula x102 = x103.one();
        Expression x106 = x6.union(x7);
        Expression x105 = x106.union(Expression.INTS);
        Formula x104 = x103.in(x105);
        Formula x101 = x102.and(x104);
        Formula x98 = x101.forAll(x99);
        Formula x80 = x81.and(x98);
        Formula x77 = x80.forAll(x78);
        Expression x109 = x14.join(Expression.UNIV);
        Expression x108 = x109.join(Expression.UNIV);
        Formula x107 = x108.in(x10);
        Variable x112 = Variable.unary("p1_this");
        Decls x111 = x112.oneOf(x11);
        Expression x114 = x112.join(x15);
        Expression x117 = x6.union(x7);
        Expression x116 = x117.union(Expression.INTS);
        Expression x119 = x6.union(x7);
        Expression x118 = x119.union(Expression.INTS);
        Expression x115 = x116.product(x118);
        Formula x113 = x114.in(x115);
        Formula x110 = x113.forAll(x111);
        Expression x122 = x15.join(Expression.UNIV);
        Expression x121 = x122.join(Expression.UNIV);
        Formula x120 = x121.in(x11);
        Variable x126 = Variable.unary("p1_r1");
        Decls x125 = x126.oneOf(x8);
        Variable x129 = Variable.unary("p1_x");
        Expression x130 = x6.union(x7);
        Decls x128 = x129.oneOf(x130);
        Expression x133 = x126.join(x12);
        Expression x132 = x129.join(x133);
        Formula x131 = x132.one();
        Formula x127 = x131.forAll(x128);
        Formula x124 = x127.forAll(x125);
        Formula x123 = x124.not();
        Formula x134 = x0.eq(x0);
        Formula x135 = x1.eq(x1);
        Formula x136 = x2.eq(x2);
        Formula x137 = x3.eq(x3);
        Formula x138 = x4.eq(x4);
        Formula x139 = x5.eq(x5);
        Formula x140 = x6.eq(x6);
        Formula x141 = x7.eq(x7);
        Formula x142 = x8.eq(x8);
        Formula x143 = x9.eq(x9);
        Formula x144 = x10.eq(x10);
        Formula x145 = x11.eq(x11);
        Formula x146 = x12.eq(x12);
        Formula x147 = x13.eq(x13);
        Formula x148 = x14.eq(x14);
        Formula x149 = x15.eq(x15);
        Formula x16 = Formula.compose(FormulaOperator.AND, x17, x41, x45, x74, x77, x107, x110,
                x120, x123, x134, x135, x136, x137, x138, x139, x140, x141, x142, x143, x144, x145,
                x146, x147, x148, x149);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        //solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x16, bounds);
        System.out.println(sol.toString());
    }
}
