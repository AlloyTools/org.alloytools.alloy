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

public final class Test {

    public static void main(String[] args) throws Exception {

        Relation x0 = Relation.unary("Int/min");
        Relation x1 = Relation.unary("Int/zero");
        Relation x2 = Relation.unary("Int/max");
        Relation x3 = Relation.nary("Int/next", 2);
        Relation x4 = Relation.unary("seq/Int");
        Relation x5 = Relation.unary("String");
        Relation x6 = Relation.unary("this/Book");
        Relation x7 = Relation.unary("this/Name");
        Relation x8 = Relation.unary("this/Addr");
        Relation x9 = Relation.unary("this/AddBX");
        Relation x10 = Relation.nary("this/AddBX.addr", 4);

        List<String> atomlist = Arrays.asList("-1", "-2", "-3", "-4", "-5", "-6", "-7", "-8", "0", "1", "2", "3", "4",
                "5", "6", "7", "AddBX$0", "AddBX$1", "AddBX$2", "AddBX$3", "Addr$0", "Addr$1", "Addr$2", "Addr$3",
                "Book$0", "Book$1", "Book$2", "Book$3", "Name$0", "Name$1", "Name$2", "Name$3");

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
        x4_upper.add(factory.tuple("3"));
        bounds.boundExactly(x4, x4_upper);

        TupleSet x5_upper = factory.noneOf(1);
        bounds.boundExactly(x5, x5_upper);

        TupleSet x6_upper = factory.noneOf(1);
        x6_upper.add(factory.tuple("Book$0"));
        x6_upper.add(factory.tuple("Book$1"));
        x6_upper.add(factory.tuple("Book$2"));
        x6_upper.add(factory.tuple("Book$3"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("Name$0"));
        x7_upper.add(factory.tuple("Name$1"));
        x7_upper.add(factory.tuple("Name$2"));
        x7_upper.add(factory.tuple("Name$3"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("Addr$0"));
        x8_upper.add(factory.tuple("Addr$1"));
        x8_upper.add(factory.tuple("Addr$2"));
        x8_upper.add(factory.tuple("Addr$3"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("AddBX$0"));
        x9_upper.add(factory.tuple("AddBX$1"));
        x9_upper.add(factory.tuple("AddBX$2"));
        x9_upper.add(factory.tuple("AddBX$3"));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(4);
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$1").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$2").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$0")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$1")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$2")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$2"))
                .product(factory.tuple("Addr$3")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$2")));
        x10_upper.add(factory.tuple("AddBX$3").product(factory.tuple("Book$3")).product(factory.tuple("Name$3"))
                .product(factory.tuple("Addr$3")));
        bounds.bound(x10, x10_upper);

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

        Variable x14 = Variable.unary("XRun_this");
        Decls x13 = x14.oneOf(x9);
        Expression x18 = x14.join(x10);
        Expression x20 = x6.product(x7);
        Expression x19 = x20.product(x8);
        Formula x17 = x18.in(x19);
        Variable x24 = Variable.unary("");
        Decls x23 = x24.oneOf(Expression.UNIV);
        Variable x27 = Variable.unary("");
        Decls x26 = x27.oneOf(Expression.UNIV);
        Decls x22 = x23.and(x26);
        Expression x30 = x27.product(x24);
        Expression x31 = x6.product(x7);
        Formula x29 = x30.in(x31);
        Expression x35 = x27.join(x18);
        Expression x34 = x24.join(x35);
        Formula x33 = x34.lone();
        Formula x36 = x34.in(x8);
        Formula x32 = x33.and(x36);
        Formula x28 = x29.implies(x32);
        Formula x21 = x28.forAll(x22);
        Formula x16 = x17.and(x21);
        Variable x39 = Variable.unary("");
        Decls x38 = x39.oneOf(x8);
        Expression x41 = x18.join(x39);
        Expression x42 = x6.product(x7);
        Formula x40 = x41.in(x42);
        Formula x37 = x40.forAll(x38);
        Formula x15 = x16.and(x37);
        Formula x12 = x15.forAll(x13);
        Expression x46 = x10.join(Expression.UNIV);
        Expression x45 = x46.join(Expression.UNIV);
        Expression x44 = x45.join(Expression.UNIV);
        Formula x43 = x44.in(x9);
        Variable x50 = Variable.unary("XRun_B");
        Decls x49 = x50.oneOf(x6);
        Variable x52 = Variable.unary("XRun_N");
        Decls x51 = x52.oneOf(x7);
        Variable x54 = Variable.unary("XRun_X");
        Decls x53 = x54.oneOf(x9);
        Decls x48 = x49.and(x51).and(x53);
        Expression x59 = x54.join(x10);
        Expression x58 = x50.join(x59);
        Expression x57 = x52.join(x58);
        IntExpression x56 = x57.count();
        IntExpression x60 = IntConstant.constant(2);
        Formula x55 = x56.eq(x60);
        Formula x47 = x55.forSome(x48);
        Formula x61 = x0.eq(x0);
        Formula x62 = x1.eq(x1);
        Formula x63 = x2.eq(x2);
        Formula x64 = x3.eq(x3);
        Formula x65 = x4.eq(x4);
        Formula x66 = x5.eq(x5);
        Formula x67 = x6.eq(x6);
        Formula x68 = x7.eq(x7);
        Formula x69 = x8.eq(x8);
        Formula x70 = x9.eq(x9);
        Formula x71 = x10.eq(x10);
        Formula x11 = Formula.compose(FormulaOperator.AND, x12, x43, x47, x61, x62, x63, x64, x65, x66, x67, x68, x69,
                x70, x71);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
        // solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);

        System.out.println(PrettyPrinter.print(x11, 4));

        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x11, bounds);
        System.out.println(sol.toString());
    }
}
