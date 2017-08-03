package tmp;

import java.util.Arrays;
import java.util.List;
import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.Options;

/* 
==================================================
  kodkod formula: 
==================================================
  (all XRun_this: this/AddBX | 
    (XRun_this . this/AddBX.addr) in (this/Book -> this/Name -> this/Addr) && 
    (all v20: project[this/Book -> this/Name, <0>], v19: project[this/Book -> 
     this/Name, <1>] | 
      (v19 -> v20) in (this/Book -> this/Name) => 
      (lone (v20 . (v19 . (XRun_this . this/AddBX.addr))) && 
       (v20 . (v19 . (XRun_this . this/AddBX.addr))) in this/Addr)) && 
    (all v21: this/Addr | 
      ((XRun_this . this/AddBX.addr) . v21) in (this/Book -> this/Name))) && 
  (((this/AddBX.addr . univ) . univ) . univ) in this/AddBX && 
  (some XRun_B: this/Book, XRun_N: this/Name, XRun_X: this/AddBX | 
    #(XRun_N . (XRun_B . (XRun_X . this/AddBX.addr))) = 2) && 
  Int/min = Int/min && 
  Int/zero = Int/zero && 
  Int/max = Int/max && 
  Int/next = Int/next && 
  seq/Int = seq/Int && 
  String = String && 
  this/Book = this/Book && 
  this/Name = this/Name && 
  this/Addr = this/Addr && 
  this/AddBX = this/AddBX && 
  this/AddBX.addr = this/AddBX.addr
==================================================
*/
public final class Test1 {

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
                "5", "6", "7", "AddBX$0", "Addr$0", "Addr$1", "Book$0", "Book$1", "Name$0", "Name$1", "unused0",
                "unused1", "unused2", "unused3", "unused4", "unused5", "unused6", "unused7", "unused8");

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
        x6_upper.add(factory.tuple("unused0"));
        x6_upper.add(factory.tuple("unused1"));
        x6_upper.add(factory.tuple("Book$0"));
        x6_upper.add(factory.tuple("Book$1"));
        bounds.bound(x6, x6_upper);

        TupleSet x7_upper = factory.noneOf(1);
        x7_upper.add(factory.tuple("unused2"));
        x7_upper.add(factory.tuple("unused3"));
        x7_upper.add(factory.tuple("Name$0"));
        x7_upper.add(factory.tuple("Name$1"));
        bounds.bound(x7, x7_upper);

        TupleSet x8_upper = factory.noneOf(1);
        x8_upper.add(factory.tuple("unused4"));
        x8_upper.add(factory.tuple("unused5"));
        x8_upper.add(factory.tuple("Addr$0"));
        x8_upper.add(factory.tuple("Addr$1"));
        bounds.bound(x8, x8_upper);

        TupleSet x9_upper = factory.noneOf(1);
        x9_upper.add(factory.tuple("unused6"));
        x9_upper.add(factory.tuple("unused7"));
        x9_upper.add(factory.tuple("unused8"));
        x9_upper.add(factory.tuple("AddBX$0"));
        bounds.bound(x9, x9_upper);

        TupleSet x10_upper = factory.noneOf(4);
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused6").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused7").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("unused8").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("unused1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$0")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused2"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("unused3"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$0"))
                .product(factory.tuple("Addr$1")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused4")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("unused5")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$0")));
        x10_upper.add(factory.tuple("AddBX$0").product(factory.tuple("Book$1")).product(factory.tuple("Name$1"))
                .product(factory.tuple("Addr$1")));
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
        Variable x24 = Variable.unary("v20");
        IntExpression x26 = IntConstant.constant(0);
        Expression x25 = x20.project(x26);
        Decls x23 = x24.oneOf(x25);
        Variable x28 = Variable.unary("v19");
        IntExpression x30 = IntConstant.constant(1);
        Expression x29 = x20.project(x30);
        Decls x27 = x28.oneOf(x29);
        Decls x22 = x23.and(x27);
        Expression x33 = x28.product(x24);
        Expression x34 = x6.product(x7);
        Formula x32 = x33.in(x34);
        Expression x38 = x28.join(x18);
        Expression x37 = x24.join(x38);
        Formula x36 = x37.lone();
        Formula x39 = x37.in(x8);
        Formula x35 = x36.and(x39);
        Formula x31 = x32.implies(x35);
        Formula x21 = x31.forAll(x22);
        Formula x16 = x17.and(x21);
        Variable x42 = Variable.unary("v21");
        Decls x41 = x42.oneOf(x8);
        Expression x44 = x18.join(x42);
        Expression x45 = x6.product(x7);
        Formula x43 = x44.in(x45);
        Formula x40 = x43.forAll(x41);
        Formula x15 = x16.and(x40);
        Formula x12 = x15.forAll(x13);
        Expression x49 = x10.join(Expression.UNIV);
        Expression x48 = x49.join(Expression.UNIV);
        Expression x47 = x48.join(Expression.UNIV);
        Formula x46 = x47.in(x9);
        Variable x54 = Variable.unary("XRun_B");
        Decls x53 = x54.oneOf(x6);
        Variable x56 = Variable.unary("XRun_N");
        Decls x55 = x56.oneOf(x7);
        Variable x58 = Variable.unary("XRun_X");
        Decls x57 = x58.oneOf(x9);
        Decls x52 = x53.and(x55).and(x57);
        Expression x63 = x58.join(x10);
        Expression x62 = x54.join(x63);
        Expression x61 = x56.join(x62);
        IntExpression x60 = x61.count();
        IntExpression x64 = IntConstant.constant(2);
        Formula x59 = x60.eq(x64);
        Formula x51 = x59.forSome(x52);
        Formula x65 = x0.eq(x0);
        Formula x66 = x1.eq(x1);
        Formula x67 = x2.eq(x2);
        Formula x68 = x3.eq(x3);
        Formula x69 = x4.eq(x4);
        Formula x70 = x5.eq(x5);
        Formula x71 = x6.eq(x6);
        Formula x72 = x7.eq(x7);
        Formula x73 = x8.eq(x8);
        Formula x74 = x9.eq(x9);
        Formula x75 = x10.eq(x10);
        Formula x11 = Formula.compose(FormulaOperator.AND, x12, x46, x51, x65, x66, x67, x68, x69, x70, x71, x72, x73,
                x74, x75);

        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        solver.options().setBitwidth(4);
//        solver.options().setFlatten(false);
        solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
        solver.options().setSymmetryBreaking(20);
        solver.options().setSkolemDepth(0);
        System.out.println("Solving...");
        System.out.flush();
        Solution sol = solver.solve(x11, bounds);
        System.out.println(sol.toString());
    }
}
