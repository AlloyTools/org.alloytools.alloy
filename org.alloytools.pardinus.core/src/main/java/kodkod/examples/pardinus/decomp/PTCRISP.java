package kodkod.examples.pardinus.decomp;

import java.util.Arrays;
import java.util.List;

import kodkod.ast.*;
import kodkod.ast.operator.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.DecomposedOptions.DMode;

public class PTCRISP {

	static Relation x0 = Relation.nary("Int/next", 2);
	static Relation x1 = Relation.unary("seq/Int");
	static Relation x2 = Relation.unary("String");
	static Relation x3 = Relation.unary("this/Key0");
	static Relation x4 = Relation.unary("this/Key1");
	static Relation x5 = Relation.unary("this/Key2");
	static Relation x6 = Relation.unary("this/Key remainder");
	static Relation x7 = Relation.unary("this/Putcode0");
	static Relation x8 = Relation.unary("this/Putcode1");
	static Relation x9 = Relation.unary("this/Putcode2");
	static Relation x10 = Relation.unary("this/Putcode3");
	static Relation x11 = Relation.unary("this/Putcode4");
	static Relation x12 = Relation.unary("this/Putcode remainder");
	static Relation x13 = Relation.unary("this/DOI1");
	static Relation x14 = Relation.unary("this/DOI2");
	static Relation x15 = Relation.unary("this/EID0");
	static Relation x16 = Relation.unary("this/EID1");
	static Relation x17 = Relation.unary("this/DOI0");
	static Relation x18 = Relation.unary("this/Handle1");
	static Relation x19 = Relation.unary("this/Handle0");
	static Relation x20 = Relation.unary("this/UID remainder");
	static Relation x21 = Relation.unary("this/Metadata0");
	static Relation x22 = Relation.unary("this/Metadata1");
	static Relation x23 = Relation.unary("this/Metadata2");
	static Relation x24 = Relation.unary("this/Metadata3");
	static Relation x25 = Relation.unary("this/Metadata remainder");
	static Relation x26 = Relation.unary("this/PTCRIS");
	static Relation x27 = Relation.unary("this/User");
	static Relation x28 = Relation.unary("this/Scopus");
	static Relation x29 = Relation.unary("this/Work0");
	static Relation x30 = Relation.unary("this/Work1");
	static Relation x31 = Relation.unary("this/Work2");
	static Relation x32 = Relation.unary("this/Work3");
	static Relation x33 = Relation.unary("this/Work4");
	static Relation x34 = Relation.unary("this/Work remainder");
	static Relation x35 = Relation.unary("this/Group0");
	static Relation x36 = Relation.unary("this/Group1");
	static Relation x37 = Relation.unary("this/Group2");
	static Relation x38 = Relation.unary("this/Group3");
	static Relation x39 = Relation.unary("this/Group4");
	static Relation x40 = Relation.unary("this/Group remainder");
	static Relation x41 = Relation.unary("this/Production0");
	static Relation x42 = Relation.unary("this/Production1");
	static Relation x43 = Relation.unary("this/Production2");
	static Relation x44 = Relation.unary("this/Production remainder");
	static Relation x45 = Relation.unary("this/Creation");
	static Relation x46 = Relation.unary("this/Modification");
	static Relation orcid = Relation.unary("this/ORCID");
	static Relation ptcris = Relation.unary("this/PTCris");
	static Relation x49 = Relation.unary("ordering/Ord");
	static Relation x50 = Relation.unary("open$3/Ord");
	static Relation x51 = Relation.unary("open$4/Ord");
	static Relation x52 = Relation.unary("open$5/Ord");
	static Relation uids = Relation.nary("this/Output.uids", 3);
	static Relation outputs = Relation.nary("this/Repository.outputs", 2);
	static Relation x55 = Relation.nary("this/Work.putcode", 2);
	static Relation x56 = Relation.nary("this/Work.source", 2);
	static Relation x57 = Relation.nary("this/Work.metadata", 2);
	static Relation x58 = Relation.nary("this/Group.works", 2);
	static Relation groups = Relation.nary("this/ORCID.groups", 2);
	static Relation x60 = Relation.nary("this/Production.key", 2);
	static Relation x61 = Relation.nary("this/Production.metadata", 2);
	static Relation x62 = Relation.nary("this/Notification.key", 2);
	static Relation x63 = Relation.nary("this/Creation.metadata", 2);
	static Relation productions = Relation.nary("this/PTCris.productions", 2);
	static Relation exported = Relation.nary("this/PTCris.exported", 2);
	static Relation notifications = Relation.nary("this/PTCris.notifications", 2);
	static Relation x67 = Relation.unary("ordering/Ord.First");
	static Relation x68 = Relation.nary("ordering/Ord.Next", 2);
	static Relation x69 = Relation.unary("open$3/Ord.First");
	static Relation x70 = Relation.nary("open$3/Ord.Next", 2);
	static Relation x71 = Relation.unary("open$4/Ord.First");
	static Relation x72 = Relation.nary("open$4/Ord.Next", 2);
	static Relation x73 = Relation.nary("open$5/Ord.First", 2);
	static Relation x74 = Relation.nary("open$5/Ord.Next", 3);
	static Relation x75 = Relation.unary("");
	static Relation x76 = Relation.unary("");

	static Universe universe;

	public static Bounds bounds1() {
		TupleFactory factory = universe.factory();
		Bounds bounds = new Bounds(universe);

		TupleSet x0_upper = factory.noneOf(2);
		bounds.boundExactly(x0, x0_upper);

		TupleSet x1_upper = factory.noneOf(1);
		bounds.boundExactly(x1, x1_upper);

		TupleSet x2_upper = factory.noneOf(1);
		bounds.boundExactly(x2, x2_upper);

		TupleSet x3_upper = factory.noneOf(1);
		x3_upper.add(factory.tuple("Key0$0"));
		bounds.boundExactly(x3, x3_upper);

		TupleSet x4_upper = factory.noneOf(1);
		x4_upper.add(factory.tuple("Key1$0"));
		bounds.boundExactly(x4, x4_upper);

		TupleSet x5_upper = factory.noneOf(1);
		x5_upper.add(factory.tuple("Key2$0"));
		bounds.boundExactly(x5, x5_upper);

		TupleSet x6_upper = factory.noneOf(1);
		x6_upper.add(factory.tuple("unused0"));
		x6_upper.add(factory.tuple("unused1"));
		x6_upper.add(factory.tuple("unused2"));
		x6_upper.add(factory.tuple("Key$0"));
		bounds.bound(x6, x6_upper);

		TupleSet x7_upper = factory.noneOf(1);
		x7_upper.add(factory.tuple("Putcode0$0"));
		bounds.boundExactly(x7, x7_upper);

		TupleSet x8_upper = factory.noneOf(1);
		x8_upper.add(factory.tuple("Putcode1$0"));
		bounds.boundExactly(x8, x8_upper);

		TupleSet x9_upper = factory.noneOf(1);
		x9_upper.add(factory.tuple("Putcode2$0"));
		bounds.boundExactly(x9, x9_upper);

		TupleSet x10_upper = factory.noneOf(1);
		x10_upper.add(factory.tuple("Putcode3$0"));
		bounds.boundExactly(x10, x10_upper);

		TupleSet x11_upper = factory.noneOf(1);
		x11_upper.add(factory.tuple("Putcode4$0"));
		bounds.boundExactly(x11, x11_upper);

		TupleSet x12_upper = factory.noneOf(1);
		x12_upper.add(factory.tuple("unused3"));
		x12_upper.add(factory.tuple("Putcode$0"));
		bounds.bound(x12, x12_upper);

		TupleSet x13_upper = factory.noneOf(1);
		x13_upper.add(factory.tuple("DOI1$0"));
		bounds.boundExactly(x13, x13_upper);

		TupleSet x14_upper = factory.noneOf(1);
		x14_upper.add(factory.tuple("DOI2$0"));
		bounds.boundExactly(x14, x14_upper);

		TupleSet x15_upper = factory.noneOf(1);
		x15_upper.add(factory.tuple("EID0$0"));
		bounds.boundExactly(x15, x15_upper);

		TupleSet x16_upper = factory.noneOf(1);
		x16_upper.add(factory.tuple("EID1$0"));
		bounds.boundExactly(x16, x16_upper);

		TupleSet x17_upper = factory.noneOf(1);
		x17_upper.add(factory.tuple("DOI0$0"));
		bounds.boundExactly(x17, x17_upper);

		TupleSet x18_upper = factory.noneOf(1);
		x18_upper.add(factory.tuple("Handle1$0"));
		bounds.boundExactly(x18, x18_upper);

		TupleSet x19_upper = factory.noneOf(1);
		x19_upper.add(factory.tuple("Handle0$0"));
		bounds.boundExactly(x19, x19_upper);

		TupleSet x20_upper = factory.noneOf(1);
		bounds.boundExactly(x20, x20_upper);

		TupleSet x21_upper = factory.noneOf(1);
		x21_upper.add(factory.tuple("Metadata0$0"));
		bounds.boundExactly(x21, x21_upper);

		TupleSet x22_upper = factory.noneOf(1);
		x22_upper.add(factory.tuple("Metadata1$0"));
		bounds.boundExactly(x22, x22_upper);

		TupleSet x23_upper = factory.noneOf(1);
		x23_upper.add(factory.tuple("Metadata2$0"));
		bounds.boundExactly(x23, x23_upper);

		TupleSet x24_upper = factory.noneOf(1);
		x24_upper.add(factory.tuple("Metadata3$0"));
		bounds.boundExactly(x24, x24_upper);

		TupleSet x25_upper = factory.noneOf(1);
		x25_upper.add(factory.tuple("unused4"));
		x25_upper.add(factory.tuple("Metadata$0"));
		x25_upper.add(factory.tuple("Metadata$1"));
		bounds.bound(x25, x25_upper);

		TupleSet x26_upper = factory.noneOf(1);
		x26_upper.add(factory.tuple("PTCRIS$0"));
		bounds.boundExactly(x26, x26_upper);

		TupleSet x27_upper = factory.noneOf(1);
		x27_upper.add(factory.tuple("User$0"));
		bounds.boundExactly(x27, x27_upper);

		TupleSet x28_upper = factory.noneOf(1);
		x28_upper.add(factory.tuple("Scopus$0"));
		bounds.boundExactly(x28, x28_upper);

		TupleSet x29_upper = factory.noneOf(1);
		x29_upper.add(factory.tuple("Work0$0"));
		bounds.boundExactly(x29, x29_upper);

		TupleSet x30_upper = factory.noneOf(1);
		x30_upper.add(factory.tuple("Work1$0"));
		bounds.boundExactly(x30, x30_upper);

		TupleSet x31_upper = factory.noneOf(1);
		x31_upper.add(factory.tuple("Work2$0"));
		bounds.boundExactly(x31, x31_upper);

		TupleSet x32_upper = factory.noneOf(1);
		x32_upper.add(factory.tuple("Work3$0"));
		bounds.boundExactly(x32, x32_upper);

		TupleSet x33_upper = factory.noneOf(1);
		x33_upper.add(factory.tuple("Work4$0"));
		bounds.boundExactly(x33, x33_upper);

		TupleSet x34_upper = factory.noneOf(1);
		bounds.boundExactly(x34, x34_upper);

		TupleSet x35_upper = factory.noneOf(1);
		x35_upper.add(factory.tuple("Group0$0"));
		bounds.boundExactly(x35, x35_upper);

		TupleSet x36_upper = factory.noneOf(1);
		x36_upper.add(factory.tuple("Group1$0"));
		bounds.boundExactly(x36, x36_upper);

		TupleSet x37_upper = factory.noneOf(1);
		x37_upper.add(factory.tuple("Group2$0"));
		bounds.boundExactly(x37, x37_upper);

		TupleSet x38_upper = factory.noneOf(1);
		x38_upper.add(factory.tuple("Group3$0"));
		bounds.boundExactly(x38, x38_upper);

		TupleSet x39_upper = factory.noneOf(1);
		x39_upper.add(factory.tuple("Group4$0"));
		bounds.boundExactly(x39, x39_upper);

		TupleSet x40_upper = factory.noneOf(1);
		bounds.boundExactly(x40, x40_upper);

		TupleSet x41_upper = factory.noneOf(1);
		x41_upper.add(factory.tuple("Production0$0"));
		bounds.boundExactly(x41, x41_upper);

		TupleSet x42_upper = factory.noneOf(1);
		x42_upper.add(factory.tuple("Production1$0"));
		bounds.boundExactly(x42, x42_upper);

		TupleSet x43_upper = factory.noneOf(1);
		x43_upper.add(factory.tuple("Production2$0"));
		bounds.boundExactly(x43, x43_upper);

		TupleSet x44_upper = factory.noneOf(1);
		x44_upper.add(factory.tuple("Production$0"));
		x44_upper.add(factory.tuple("Production$1"));
		x44_upper.add(factory.tuple("Creation$0"));
		bounds.bound(x44, x44_upper);

		TupleSet x45_upper = factory.noneOf(1);
		x45_upper.add(factory.tuple("Production$0"));
		x45_upper.add(factory.tuple("Production$1"));
		x45_upper.add(factory.tuple("Creation$0"));
		bounds.bound(x45, x45_upper);

		TupleSet x46_upper = factory.noneOf(1);
		x46_upper.add(factory.tuple("Production$0"));
		x46_upper.add(factory.tuple("Production$1"));
		x46_upper.add(factory.tuple("Creation$0"));
		bounds.bound(x46, x46_upper);

		TupleSet x49_upper = factory.noneOf(1);
		x49_upper.add(factory.tuple("ordering/Ord$0"));
		bounds.boundExactly(x49, x49_upper);

		TupleSet x50_upper = factory.noneOf(1);
		x50_upper.add(factory.tuple("open$3/Ord$0"));
		bounds.boundExactly(x50, x50_upper);

		TupleSet x51_upper = factory.noneOf(1);
		x51_upper.add(factory.tuple("open$4/Ord$0"));
		bounds.boundExactly(x51, x51_upper);

		TupleSet x52_upper = factory.noneOf(1);
		x52_upper.add(factory.tuple("open$5/Ord$0"));
		bounds.boundExactly(x52, x52_upper);

		TupleSet x55_upper = factory.noneOf(2);
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode0$0")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode1$0")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode2$0")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode3$0")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode4$0")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("unused3")));
		x55_upper.add(factory.tuple("Work0$0").product(factory.tuple("Putcode$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode0$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode1$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode2$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode3$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode4$0")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("unused3")));
		x55_upper.add(factory.tuple("Work1$0").product(factory.tuple("Putcode$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode0$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode1$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode2$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode3$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode4$0")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("unused3")));
		x55_upper.add(factory.tuple("Work2$0").product(factory.tuple("Putcode$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode0$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode1$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode2$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode3$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode4$0")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("unused3")));
		x55_upper.add(factory.tuple("Work3$0").product(factory.tuple("Putcode$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode0$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode1$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode2$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode3$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode4$0")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("unused3")));
		x55_upper.add(factory.tuple("Work4$0").product(factory.tuple("Putcode$0")));
		bounds.bound(x55, x55_upper);

		TupleSet x56_upper = factory.noneOf(2);
		x56_upper.add(factory.tuple("Work0$0").product(factory.tuple("PTCRIS$0")));
		x56_upper.add(factory.tuple("Work0$0").product(factory.tuple("User$0")));
		x56_upper.add(factory.tuple("Work0$0").product(factory.tuple("Scopus$0")));
		x56_upper.add(factory.tuple("Work1$0").product(factory.tuple("PTCRIS$0")));
		x56_upper.add(factory.tuple("Work1$0").product(factory.tuple("User$0")));
		x56_upper.add(factory.tuple("Work1$0").product(factory.tuple("Scopus$0")));
		x56_upper.add(factory.tuple("Work2$0").product(factory.tuple("PTCRIS$0")));
		x56_upper.add(factory.tuple("Work2$0").product(factory.tuple("User$0")));
		x56_upper.add(factory.tuple("Work2$0").product(factory.tuple("Scopus$0")));
		x56_upper.add(factory.tuple("Work3$0").product(factory.tuple("PTCRIS$0")));
		x56_upper.add(factory.tuple("Work3$0").product(factory.tuple("User$0")));
		x56_upper.add(factory.tuple("Work3$0").product(factory.tuple("Scopus$0")));
		x56_upper.add(factory.tuple("Work4$0").product(factory.tuple("PTCRIS$0")));
		x56_upper.add(factory.tuple("Work4$0").product(factory.tuple("User$0")));
		x56_upper.add(factory.tuple("Work4$0").product(factory.tuple("Scopus$0")));
		bounds.bound(x56, x56_upper);

		TupleSet x57_upper = factory.noneOf(2);
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata0$0")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata1$0")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata2$0")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata3$0")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("unused4")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata$0")));
		x57_upper.add(factory.tuple("Work0$0").product(factory.tuple("Metadata$1")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata0$0")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata1$0")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata2$0")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata3$0")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("unused4")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata$0")));
		x57_upper.add(factory.tuple("Work1$0").product(factory.tuple("Metadata$1")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata0$0")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata1$0")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata2$0")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata3$0")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("unused4")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata$0")));
		x57_upper.add(factory.tuple("Work2$0").product(factory.tuple("Metadata$1")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata0$0")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata1$0")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata2$0")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata3$0")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("unused4")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata$0")));
		x57_upper.add(factory.tuple("Work3$0").product(factory.tuple("Metadata$1")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata0$0")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata1$0")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata2$0")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata3$0")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("unused4")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata$0")));
		x57_upper.add(factory.tuple("Work4$0").product(factory.tuple("Metadata$1")));
		bounds.bound(x57, x57_upper);

		TupleSet x58_upper = factory.noneOf(2);
		x58_upper.add(factory.tuple("Group0$0").product(factory.tuple("Work0$0")));
		x58_upper.add(factory.tuple("Group0$0").product(factory.tuple("Work1$0")));
		x58_upper.add(factory.tuple("Group0$0").product(factory.tuple("Work2$0")));
		x58_upper.add(factory.tuple("Group0$0").product(factory.tuple("Work3$0")));
		x58_upper.add(factory.tuple("Group0$0").product(factory.tuple("Work4$0")));
		x58_upper.add(factory.tuple("Group1$0").product(factory.tuple("Work0$0")));
		x58_upper.add(factory.tuple("Group1$0").product(factory.tuple("Work1$0")));
		x58_upper.add(factory.tuple("Group1$0").product(factory.tuple("Work2$0")));
		x58_upper.add(factory.tuple("Group1$0").product(factory.tuple("Work3$0")));
		x58_upper.add(factory.tuple("Group1$0").product(factory.tuple("Work4$0")));
		x58_upper.add(factory.tuple("Group2$0").product(factory.tuple("Work0$0")));
		x58_upper.add(factory.tuple("Group2$0").product(factory.tuple("Work1$0")));
		x58_upper.add(factory.tuple("Group2$0").product(factory.tuple("Work2$0")));
		x58_upper.add(factory.tuple("Group2$0").product(factory.tuple("Work3$0")));
		x58_upper.add(factory.tuple("Group2$0").product(factory.tuple("Work4$0")));
		x58_upper.add(factory.tuple("Group3$0").product(factory.tuple("Work0$0")));
		x58_upper.add(factory.tuple("Group3$0").product(factory.tuple("Work1$0")));
		x58_upper.add(factory.tuple("Group3$0").product(factory.tuple("Work2$0")));
		x58_upper.add(factory.tuple("Group3$0").product(factory.tuple("Work3$0")));
		x58_upper.add(factory.tuple("Group3$0").product(factory.tuple("Work4$0")));
		x58_upper.add(factory.tuple("Group4$0").product(factory.tuple("Work0$0")));
		x58_upper.add(factory.tuple("Group4$0").product(factory.tuple("Work1$0")));
		x58_upper.add(factory.tuple("Group4$0").product(factory.tuple("Work2$0")));
		x58_upper.add(factory.tuple("Group4$0").product(factory.tuple("Work3$0")));
		x58_upper.add(factory.tuple("Group4$0").product(factory.tuple("Work4$0")));
		bounds.bound(x58, x58_upper);

		TupleSet x60_upper = factory.noneOf(2);
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Production0$0").product(factory.tuple("Key$0")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Production1$0").product(factory.tuple("Key$0")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Production2$0").product(factory.tuple("Key$0")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Production$0").product(factory.tuple("Key$0")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Production$1").product(factory.tuple("Key$0")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key0$0")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key1$0")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key2$0")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused0")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused1")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused2")));
		x60_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key$0")));
		bounds.bound(x60, x60_upper);

		TupleSet x61_upper = factory.noneOf(2);
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Production0$0").product(factory.tuple("Metadata$1")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Production1$0").product(factory.tuple("Metadata$1")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Production2$0").product(factory.tuple("Metadata$1")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata$1")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata$1")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata0$0")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata1$0")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata2$0")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata3$0")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused4")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata$0")));
		x61_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata$1")));
		bounds.bound(x61, x61_upper);

		TupleSet x62_upper = factory.noneOf(2);
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("Key0$0")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("Key1$0")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("Key2$0")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("unused0")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("unused1")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("unused2")));
		x62_upper.add(factory.tuple("Production$0").product(factory.tuple("Key$0")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("Key0$0")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("Key1$0")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("Key2$0")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("unused0")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("unused1")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("unused2")));
		x62_upper.add(factory.tuple("Production$1").product(factory.tuple("Key$0")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key0$0")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key1$0")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key2$0")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused0")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused1")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused2")));
		x62_upper.add(factory.tuple("Creation$0").product(factory.tuple("Key$0")));
		bounds.bound(x62, x62_upper);

		TupleSet x63_upper = factory.noneOf(2);
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata0$0")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata1$0")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata2$0")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata3$0")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("unused4")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata$0")));
		x63_upper.add(factory.tuple("Production$0").product(factory.tuple("Metadata$1")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata0$0")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata1$0")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata2$0")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata3$0")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("unused4")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata$0")));
		x63_upper.add(factory.tuple("Production$1").product(factory.tuple("Metadata$1")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata0$0")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata1$0")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata2$0")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata3$0")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("unused4")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata$0")));
		x63_upper.add(factory.tuple("Creation$0").product(factory.tuple("Metadata$1")));
		bounds.bound(x63, x63_upper);

		TupleSet x71_upper = factory.noneOf(1);
		x71_upper.add(factory.tuple("Work0$0"));
		x71_upper.add(factory.tuple("Work1$0"));
		x71_upper.add(factory.tuple("Work2$0"));
		x71_upper.add(factory.tuple("Work3$0"));
		x71_upper.add(factory.tuple("Work4$0"));
		bounds.bound(x71, x71_upper);

		TupleSet x72_upper = factory.noneOf(2);
		x72_upper.add(factory.tuple("Work0$0").product(factory.tuple("Work0$0")));
		x72_upper.add(factory.tuple("Work0$0").product(factory.tuple("Work1$0")));
		x72_upper.add(factory.tuple("Work0$0").product(factory.tuple("Work2$0")));
		x72_upper.add(factory.tuple("Work0$0").product(factory.tuple("Work3$0")));
		x72_upper.add(factory.tuple("Work0$0").product(factory.tuple("Work4$0")));
		x72_upper.add(factory.tuple("Work1$0").product(factory.tuple("Work0$0")));
		x72_upper.add(factory.tuple("Work1$0").product(factory.tuple("Work1$0")));
		x72_upper.add(factory.tuple("Work1$0").product(factory.tuple("Work2$0")));
		x72_upper.add(factory.tuple("Work1$0").product(factory.tuple("Work3$0")));
		x72_upper.add(factory.tuple("Work1$0").product(factory.tuple("Work4$0")));
		x72_upper.add(factory.tuple("Work2$0").product(factory.tuple("Work0$0")));
		x72_upper.add(factory.tuple("Work2$0").product(factory.tuple("Work1$0")));
		x72_upper.add(factory.tuple("Work2$0").product(factory.tuple("Work2$0")));
		x72_upper.add(factory.tuple("Work2$0").product(factory.tuple("Work3$0")));
		x72_upper.add(factory.tuple("Work2$0").product(factory.tuple("Work4$0")));
		x72_upper.add(factory.tuple("Work3$0").product(factory.tuple("Work0$0")));
		x72_upper.add(factory.tuple("Work3$0").product(factory.tuple("Work1$0")));
		x72_upper.add(factory.tuple("Work3$0").product(factory.tuple("Work2$0")));
		x72_upper.add(factory.tuple("Work3$0").product(factory.tuple("Work3$0")));
		x72_upper.add(factory.tuple("Work3$0").product(factory.tuple("Work4$0")));
		x72_upper.add(factory.tuple("Work4$0").product(factory.tuple("Work0$0")));
		x72_upper.add(factory.tuple("Work4$0").product(factory.tuple("Work1$0")));
		x72_upper.add(factory.tuple("Work4$0").product(factory.tuple("Work2$0")));
		x72_upper.add(factory.tuple("Work4$0").product(factory.tuple("Work3$0")));
		x72_upper.add(factory.tuple("Work4$0").product(factory.tuple("Work4$0")));
		bounds.bound(x72, x72_upper);

		TupleSet x73_upper = factory.noneOf(2);
		x73_upper.add(factory.tuple("open$5/Ord$0").product(factory.tuple("PTCRIS$0")));
		bounds.boundExactly(x73, x73_upper);

		TupleSet x74_upper = factory.noneOf(3);
		x74_upper
				.add(factory.tuple("open$5/Ord$0").product(factory.tuple("PTCRIS$0")).product(factory.tuple("User$0")));
		x74_upper
				.add(factory.tuple("open$5/Ord$0").product(factory.tuple("User$0")).product(factory.tuple("Scopus$0")));
		bounds.boundExactly(x74, x74_upper);

		return bounds;
	}

	public static Bounds bounds2() {
		TupleFactory factory = universe.factory();
		Bounds bounds = new Bounds(universe);

		TupleSet x75_upper = factory.noneOf(1);
		x75_upper.add(factory.tuple("ORCID$0"));
		bounds.bound(x75, x75_upper);

		TupleSet x76_upper = factory.noneOf(1);
		x76_upper.add(factory.tuple("PTCris$0"));
		x76_upper.add(factory.tuple("PTCris$1"));
		bounds.bound(x76, x76_upper);

		TupleSet x59_upper = factory.noneOf(2);
		x59_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group0$0")));
		x59_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group1$0")));
		x59_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group2$0")));
		x59_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group3$0")));
		x59_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group4$0")));
		bounds.bound(groups, x59_upper);

		TupleSet x64_upper = factory.noneOf(2);
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production0$0")));
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production1$0")));
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production2$0")));
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$0")));
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$1")));
		x64_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Creation$0")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production0$0")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production1$0")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production2$0")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$0")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$1")));
		x64_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Creation$0")));
		bounds.bound(productions, x64_upper);

		TupleSet x65_upper = factory.noneOf(2);
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production0$0")));
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production1$0")));
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production2$0")));
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$0")));
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$1")));
		x65_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Creation$0")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production0$0")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production1$0")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production2$0")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$0")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$1")));
		x65_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Creation$0")));
		bounds.bound(exported, x65_upper);

		TupleSet x66_upper = factory.noneOf(2);
		x66_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$0")));
		x66_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$1")));
		x66_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Creation$0")));
		x66_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$0")));
		x66_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$1")));
		x66_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Creation$0")));
		bounds.bound(notifications, x66_upper);

		TupleSet x67_upper = factory.noneOf(1);
		x67_upper.add(factory.tuple("ORCID$0"));
		bounds.bound(x67, x67_upper);

		TupleSet x68_upper = factory.noneOf(2);
		x68_upper.add(factory.tuple("ORCID$0").product(factory.tuple("ORCID$0")));
		bounds.bound(x68, x68_upper);

		TupleSet x69_upper = factory.noneOf(1);
		x69_upper.add(factory.tuple("PTCris$0"));
		x69_upper.add(factory.tuple("PTCris$1"));
		bounds.bound(x69, x69_upper);

		TupleSet x70_upper = factory.noneOf(2);
		x70_upper.add(factory.tuple("PTCris$0").product(factory.tuple("PTCris$0")));
		x70_upper.add(factory.tuple("PTCris$0").product(factory.tuple("PTCris$1")));
		x70_upper.add(factory.tuple("PTCris$1").product(factory.tuple("PTCris$0")));
		x70_upper.add(factory.tuple("PTCris$1").product(factory.tuple("PTCris$1")));
		bounds.bound(x70, x70_upper);

		TupleSet x47_upper = factory.noneOf(1);
		x47_upper.add(factory.tuple("ORCID$0"));
		bounds.boundExactly(orcid, x47_upper);

		TupleSet x48_upper = factory.noneOf(1);
		x48_upper.add(factory.tuple("PTCris$0"));
		x48_upper.add(factory.tuple("PTCris$1"));
		bounds.boundExactly(ptcris, x48_upper);

		TupleSet x54_upper = factory.noneOf(2);
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Work0$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Work1$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Work2$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Work3$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Work4$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group0$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group1$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group2$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group3$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Group4$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Production0$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Production1$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Production2$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Production$0")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Production$1")));
		x54_upper.add(factory.tuple("ORCID$0").product(factory.tuple("Creation$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Work0$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Work1$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Work2$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Work3$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Work4$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Group0$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Group1$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Group2$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Group3$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Group4$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production0$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production1$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production2$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$0")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Production$1")));
		x54_upper.add(factory.tuple("PTCris$0").product(factory.tuple("Creation$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Work0$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Work1$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Work2$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Work3$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Work4$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Group0$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Group1$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Group2$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Group3$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Group4$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production0$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production1$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production2$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$0")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Production$1")));
		x54_upper.add(factory.tuple("PTCris$1").product(factory.tuple("Creation$0")));
		bounds.bound(outputs, x54_upper);

		TupleSet x53_upper = factory.noneOf(3);
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Work4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group0$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group1$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group2$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group3$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Group4$0").product(factory.tuple("Handle0$0")).product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production0$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production0$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production0$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production0$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production0$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production0$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production1$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production1$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production1$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production1$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production1$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production1$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production2$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production2$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI2$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production2$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("EID0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production2$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("EID1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Production2$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("DOI0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production2$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper
				.add(factory.tuple("Production$1").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Production$1").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI2$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI2$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID0$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("EID1$0")).product(factory.tuple("PTCris$1")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("DOI0$0")).product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Creation$0").product(factory.tuple("Handle1$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("Handle1$0"))
				.product(factory.tuple("PTCris$1")));
		x53_upper
				.add(factory.tuple("Creation$0").product(factory.tuple("Handle0$0")).product(factory.tuple("ORCID$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$0")));
		x53_upper.add(factory.tuple("Creation$0").product(factory.tuple("Handle0$0"))
				.product(factory.tuple("PTCris$1")));
		bounds.bound(uids, x53_upper);

		return bounds;
	}

	public static void main(String[] args) throws Exception {

		List<String> atomlist = Arrays.asList("Creation$0", "DOI0$0", "DOI1$0", "DOI2$0", "EID0$0", "EID1$0",
				"Group0$0", "Group1$0", "Group2$0", "Group3$0", "Group4$0", "Handle0$0", "Handle1$0", "Key$0",
				"Key0$0", "Key1$0", "Key2$0", "Metadata$0", "Metadata$1", "Metadata0$0", "Metadata1$0", "Metadata2$0",
				"Metadata3$0", "ORCID$0", "PTCRIS$0", "PTCris$0", "PTCris$1", "Production$0", "Production$1",
				"Production0$0", "Production1$0", "Production2$0", "Putcode$0", "Putcode0$0", "Putcode1$0",
				"Putcode2$0", "Putcode3$0", "Putcode4$0", "Scopus$0", "User$0", "Work0$0", "Work1$0", "Work2$0",
				"Work3$0", "Work4$0", "open$3/Ord$0", "open$4/Ord$0", "open$5/Ord$0", "ordering/Ord$0", "unused0",
				"unused1", "unused2", "unused3", "unused4");

		universe = new Universe(atomlist);

		// Formula x1200 = x0.eq(x0);
		// Formula x1201 = x1.eq(x1);
		// Formula x1202 = x2.eq(x2);
		// Formula x1203 = x3.eq(x3);
		// Formula x1204 = x4.eq(x4);
		// Formula x1205 = x5.eq(x5);
		// Formula x1206 = x6.eq(x6);
		// Formula x1207 = x7.eq(x7);
		// Formula x1208 = x8.eq(x8);
		// Formula x1209 = x9.eq(x9);
		// Formula x1210 = x10.eq(x10);
		// Formula x1211 = x11.eq(x11);
		// Formula x1212 = x12.eq(x12);
		// Formula x1213 = x13.eq(x13);
		// Formula x1214 = x14.eq(x14);
		// Formula x1215 = x15.eq(x15);
		// Formula x1216 = x16.eq(x16);
		// Formula x1217 = x17.eq(x17);
		// Formula x1218 = x18.eq(x18);
		// Formula x1219 = x19.eq(x19);
		// Formula x1220 = x20.eq(x20);
		// Formula x1221 = x21.eq(x21);
		// Formula x1222 = x22.eq(x22);
		// Formula x1223 = x23.eq(x23);
		// Formula x1224 = x24.eq(x24);
		// Formula x1225 = x25.eq(x25);
		// Formula x1226 = x26.eq(x26);
		// Formula x1227 = x27.eq(x27);
		// Formula x1228 = x28.eq(x28);
		// Formula x1229 = x29.eq(x29);
		// Formula x1230 = x30.eq(x30);
		// Formula x1231 = x31.eq(x31);
		// Formula x1232 = x32.eq(x32);
		// Formula x1233 = x33.eq(x33);
		// Formula x1234 = x34.eq(x34);
		// Formula x1235 = x35.eq(x35);
		// Formula x1236 = x36.eq(x36);
		// Formula x1237 = x37.eq(x37);
		// Formula x1238 = x38.eq(x38);
		// Formula x1239 = x39.eq(x39);
		// Formula x1240 = x40.eq(x40);
		// Formula x1241 = x41.eq(x41);
		// Formula x1242 = x42.eq(x42);
		// Formula x1243 = x43.eq(x43);
		// Formula x1244 = x44.eq(x44);
		// Formula x1245 = x45.eq(x45);
		// Formula x1246 = x46.eq(x46);
		// Formula x1247 = orcid.eq(orcid);
		// Formula x1248 = ptcris.eq(ptcris);
		// Formula x1249 = x49.eq(x49);
		// Formula x1250 = x50.eq(x50);
		// Formula x1251 = x51.eq(x51);
		// Formula x1252 = x52.eq(x52);
		// Formula x1253 = uids.eq(uids);
		// Formula x1254 = outputs.eq(outputs);
		// Formula x1255 = x55.eq(x55);
		// Formula x1256 = x56.eq(x56);
		// Formula x1257 = x57.eq(x57);
		// Formula x1258 = x58.eq(x58);
		// Formula x1259 = groups.eq(groups);
		// Formula x1260 = x60.eq(x60);
		// Formula x1261 = x61.eq(x61);
		// Formula x1262 = x62.eq(x62);
		// Formula x1263 = x63.eq(x63);
		// Formula x1264 = productions.eq(productions);
		// Formula x1265 = exported.eq(exported);
		// Formula x1266 = notifications.eq(notifications);
		// Formula x1267 = x67.eq(x67);
		// Formula x1268 = x68.eq(x68);
		// Formula x1269 = x69.eq(x69);
		// Formula x1270 = x70.eq(x70);
		// Formula x1271 = x71.eq(x71);
		// Formula x1272 = x72.eq(x72);
		// Formula x1273 = x73.eq(x73);
		// Formula x1274 = x74.eq(x74);
		// Formula x1275 = x75.eq(x75);
		// Formula x1276 = x76.eq(x76);
		// Formula x77 = Formula.compose(FormulaOperator.AND, f13(), b3(),
		// f12(), b1(), b2(), f11(), f10(), f9(),
		// f8(), f7(), f6(), f5(), f4(), f3(), f2(), f1(), x1200, x1201, x1202,
		// x1203, x1204, x1205, x1206, x1207,
		// x1208, x1209, x1210, x1211, x1212, x1213, x1214, x1215, x1216, x1217,
		// x1218, x1219, x1220, x1221,
		// x1222, x1223, x1224, x1225, x1226, x1227, x1228, x1229, x1230, x1231,
		// x1232, x1233, x1234, x1235,
		// x1236, x1237, x1238, x1239, x1240, x1241, x1242, x1243, x1244, x1245,
		// x1246, x1247, x1248, x1249,
		// x1250, x1251, x1252, x1253, x1254, x1255, x1256, x1257, x1258, x1259,
		// x1260, x1261, x1262, x1263,
		// x1264, x1265, x1266, x1267, x1268, x1269, x1270, x1271, x1272, x1273,
		// x1274, x1275, x1276);

//		Solver solver = new Solver();
//		solver.options().setSolver(SATFactory.Glucose);
//		solver.options().setBitwidth(1);
//		solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
//		solver.options().setSymmetryBreaking(20);
//		solver.options().setSkolemDepth(0);
//		System.out.println("Solving...");
//		System.out.flush();
//		Solution sol = solver.solve(formula1().and(formula2()), b3);
//		System.out.println(sol.toString());
		
		ExtendedOptions opt, opt2;
		
		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setThreads(4);
		opt2 = new ExtendedOptions(opt);
		opt2.setRunTarget(false);
		opt2.setReporter(new ConsoleReporter());

//		opt2.setTargetMode(TMode.FAR);
//		opt2.setSolver(SATFactory.PMaxSAT4J);
		opt.setConfigOptions(opt2);
		opt.setReporter(new ConsoleReporter());
		new PardinusSolver(opt);
		
//		Bounds b3 = bounds1();
//		Bounds b2 = bounds2();
//		for (Relation r : b2.relations()) {
//			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
//		}
		
//		Solution solution = psolver.solve(formula1(), formula2(), bounds1(), bounds2());

		

	}

	private static Formula formula1() {
		return Formula.compose(FormulaOperator.AND, b0(), b3(), b1(), b2());
	}

	private static Formula formula2() {
		return Formula.compose(FormulaOperator.AND, f13(), f12(), f11(), f10(), f9(), f8(), f7(), f6(), f5(), f4(),
				f3(), f2(), f1());
	}

	private static Formula f1() {
		Expression x156 = x41.union(x42);
		Expression x161 = x156.union(x43);
		Expression x160 = x161.union(x44);

		Variable x630 = Variable.unary("hippocratic_import_o");
		Decls x629 = x630.oneOf(orcid);
		Variable x632 = Variable.unary("hippocratic_import_p");
		Decls x631 = x632.oneOf(ptcris);
		Variable x634 = Variable.unary("hippocratic_import_p'");
		Expression x635 = x632.join(x70);
		Decls x633 = x634.oneOf(x635);
		Decls x628 = x629.and(x631).and(x633);
		Variable x643 = Variable.unary("EXPORTED_e");
		Expression x644 = x632.join(exported);
		Decls x642 = x643.oneOf(x644);
		Variable x648 = Variable.unary("EXPORTED_w");
		Expression x650 = x630.join(groups);
		Expression x649 = x650.join(x58);
		Decls x647 = x648.oneOf(x649);
		Expression x655 = x643.join(uids);
		Expression x654 = x655.join(x632);
		Expression x657 = x648.join(uids);
		Expression x656 = x657.join(x630);
		Formula x653 = x654.eq(x656);
		Expression x659 = x643.join(x61);
		Expression x660 = x648.join(x57);
		Formula x658 = x659.eq(x660);
		Formula x652 = x653.and(x658);
		Expression x662 = x648.join(x56);
		Formula x661 = x662.eq(x26);
		Formula x651 = x652.and(x661);
		Expression x646 = x651.comprehension(x647);
		Formula x645 = x646.one();
		Formula x641 = x645.forAll(x642);
		Variable x665 = Variable.unary("EXPORTED_w");
		Expression x667 = x630.join(groups);
		Expression x666 = x667.join(x58);
		Decls x664 = x665.oneOf(x666);
		Expression x671 = x665.join(x56);
		Formula x670 = x671.eq(x26);
		Formula x669 = x670.not();
		Variable x674 = Variable.unary("EXPORTED_e");
		Expression x675 = x632.join(exported);
		Decls x673 = x674.oneOf(x675);
		Expression x679 = x674.join(uids);
		Expression x678 = x679.join(x632);
		Expression x681 = x665.join(uids);
		Expression x680 = x681.join(x630);
		Formula x677 = x678.eq(x680);
		Expression x683 = x674.join(x61);
		Expression x684 = x665.join(x57);
		Formula x682 = x683.eq(x684);
		Formula x676 = x677.and(x682);
		Formula x672 = x676.forSome(x673);
		Formula x668 = x669.or(x672);
		Formula x663 = x668.forAll(x664);
		Formula x640 = x641.and(x663);
		Variable x689 = Variable.unary("IMPORTED_g");
		Expression x690 = x630.join(groups);
		Decls x688 = x689.oneOf(x690);
		Variable x693 = Variable.unary("IMPORTED_p1");
		Expression x695 = x632.join(productions);
		Expression x696 = x632.join(notifications);
		Expression x694 = x695.union(x696);
		Decls x692 = x693.oneOf(x694);
		Expression x699 = x689.join(uids);
		Expression x698 = x699.join(x630);
		Expression x701 = x693.join(uids);
		Expression x700 = x701.join(x632);
		Formula x697 = x698.in(x700);
		Formula x691 = x697.forSome(x692);
		Formula x687 = x691.forAll(x688);
		Variable x706 = Variable.unary("IMPORTED_n");
		Expression x707 = x632.join(notifications);
		Decls x705 = x706.oneOf(x707);
		Variable x710 = Variable.unary("IMPORTED_g");
		Expression x711 = x630.join(groups);
		Decls x709 = x710.oneOf(x711);
		Expression x714 = x710.join(uids);
		Expression x713 = x714.join(x630);
		Expression x716 = x706.join(uids);
		Expression x715 = x716.join(x632);
		Formula x712 = x713.eq(x715);
		Formula x708 = x712.forSome(x709);
		Formula x704 = x708.forAll(x705);
		Variable x719 = Variable.unary("IMPORTED_n");
		Expression x721 = x632.join(notifications);
		Expression x720 = x721.intersection(x45);
		Decls x718 = x719.oneOf(x720);
		Expression x725 = x719.join(uids);
		Expression x724 = x725.join(x632);
		Formula x723 = x724.some();
		Variable x728 = Variable.unary("IMPORTED_p1");
		Expression x731 = x632.join(productions);
		Expression x732 = x632.join(notifications);
		Expression x730 = x731.union(x732);
		Expression x729 = x730.difference(x719);
		Decls x727 = x728.oneOf(x729);
		Expression x737 = x719.join(uids);
		Expression x736 = x737.join(x632);
		Expression x739 = x728.join(uids);
		Expression x738 = x739.join(x632);
		Expression x735 = x736.intersection(x738);
		Formula x734 = x735.some();
		Formula x733 = x734.not();
		Formula x726 = x733.forAll(x727);
		Formula x722 = x723.and(x726);
		Formula x717 = x722.forAll(x718);
		Formula x703 = x704.and(x717);
		Variable x742 = Variable.unary("IMPORTED_n");
		Expression x744 = x632.join(notifications);
		Expression x743 = x744.intersection(x46);
		Decls x741 = x742.oneOf(x743);
		Expression x749 = x742.join(uids);
		Expression x748 = x749.join(x632);
		Expression x753 = x632.join(productions);
		Expression x756 = x742.join(x62);
		Expression x755 = x60.join(x756);
		Expression x754 = x160.intersection(x755);
		Expression x752 = x753.intersection(x754);
		Expression x751 = x752.join(uids);
		Expression x750 = x751.join(x632);
		Expression x747 = x748.intersection(x750);
		Formula x746 = x747.some();
		Expression x760 = x742.join(uids);
		Expression x759 = x760.join(x632);
		Expression x764 = x632.join(productions);
		Expression x767 = x742.join(x62);
		Expression x766 = x60.join(x767);
		Expression x765 = x160.intersection(x766);
		Expression x763 = x764.intersection(x765);
		Expression x762 = x763.join(uids);
		Expression x761 = x762.join(x632);
		Formula x758 = x759.in(x761);
		Formula x757 = x758.not();
		Formula x745 = x746.and(x757);
		Formula x740 = x745.forAll(x741);
		Formula x702 = x703.and(x740);
		Formula x686 = x687.and(x702);
		Variable x771 = Variable.unary("IMPORTED_n");
		Expression x773 = x632.join(notifications);
		Expression x772 = x773.intersection(x45);
		Decls x770 = x771.oneOf(x772);
		Variable x776 = Variable.unary("IMPORTED_g");
		Expression x777 = x630.join(groups);
		Decls x775 = x776.oneOf(x777);
		Expression x781 = x776.join(uids);
		Expression x780 = x781.join(x630);
		Expression x783 = x771.join(uids);
		Expression x782 = x783.join(x632);
		Formula x779 = x780.eq(x782);
		Expression x785 = x771.join(x63);
		Expression x788 = x776.join(x58);
		Expression x790 = x72.closure();
		Expression x789 = x788.join(x790);
		Expression x787 = x788.difference(x789);
		Expression x786 = x787.join(x57);
		Formula x784 = x785.eq(x786);
		Formula x778 = x779.and(x784);
		Formula x774 = x778.forSome(x775);
		Formula x769 = x774.forAll(x770);
		Variable x794 = Variable.unary("IMPORTED_g");
		Expression x795 = x630.join(groups);
		Decls x793 = x794.oneOf(x795);
		Variable x797 = Variable.unary("IMPORTED_p1");
		Expression x798 = x632.join(productions);
		Decls x796 = x797.oneOf(x798);
		Decls x792 = x793.and(x796);
		Expression x805 = x794.join(uids);
		Expression x804 = x805.join(x630);
		Expression x807 = x797.join(uids);
		Expression x806 = x807.join(x632);
		Expression x803 = x804.intersection(x806);
		Formula x802 = x803.some();
		Expression x811 = x794.join(uids);
		Expression x810 = x811.join(x630);
		Expression x813 = x797.join(uids);
		Expression x812 = x813.join(x632);
		Formula x809 = x810.in(x812);
		Formula x808 = x809.not();
		Formula x801 = x802.and(x808);
		Formula x800 = x801.not();
		Variable x817 = Variable.unary("IMPORTED_n");
		Expression x819 = x632.join(notifications);
		Expression x818 = x819.intersection(x46);
		Decls x816 = x817.oneOf(x818);
		Expression x822 = x817.join(x62);
		Expression x823 = x797.join(x60);
		Formula x821 = x822.eq(x823);
		Expression x826 = x817.join(uids);
		Expression x825 = x826.join(x632);
		Expression x828 = x794.join(uids);
		Expression x827 = x828.join(x630);
		Formula x824 = x825.eq(x827);
		Formula x820 = x821.and(x824);
		Expression x815 = x820.comprehension(x816);
		Formula x814 = x815.one();
		Formula x799 = x800.or(x814);
		Formula x791 = x799.forAll(x792);
		Formula x768 = x769.and(x791);
		Formula x685 = x686.and(x768);
		Formula x639 = x640.and(x685);
		Expression x833 = x634.join(exported);
		Expression x834 = x632.join(exported);
		Formula x832 = x833.eq(x834);
		Expression x836 = x634.join(productions);
		Expression x837 = x632.join(productions);
		Formula x835 = x836.eq(x837);
		Formula x831 = x832.and(x835);
		Variable x840 = Variable.unary("frame_p1");
		Expression x841 = x632.join(productions);
		Decls x839 = x840.oneOf(x841);
		Expression x844 = x840.join(uids);
		Expression x843 = x844.join(x634);
		Expression x846 = x840.join(uids);
		Expression x845 = x846.join(x632);
		Formula x842 = x843.eq(x845);
		Formula x838 = x842.forAll(x839);
		Formula x830 = x831.and(x838);
		Variable x851 = Variable.unary("IMPORTED_g");
		Expression x852 = x630.join(groups);
		Decls x850 = x851.oneOf(x852);
		Variable x855 = Variable.unary("IMPORTED_p1");
		Expression x857 = x634.join(productions);
		Expression x858 = x634.join(notifications);
		Expression x856 = x857.union(x858);
		Decls x854 = x855.oneOf(x856);
		Expression x861 = x851.join(uids);
		Expression x860 = x861.join(x630);
		Expression x863 = x855.join(uids);
		Expression x862 = x863.join(x634);
		Formula x859 = x860.in(x862);
		Formula x853 = x859.forSome(x854);
		Formula x849 = x853.forAll(x850);
		Variable x868 = Variable.unary("IMPORTED_n");
		Expression x869 = x634.join(notifications);
		Decls x867 = x868.oneOf(x869);
		Variable x872 = Variable.unary("IMPORTED_g");
		Expression x873 = x630.join(groups);
		Decls x871 = x872.oneOf(x873);
		Expression x876 = x872.join(uids);
		Expression x875 = x876.join(x630);
		Expression x878 = x868.join(uids);
		Expression x877 = x878.join(x634);
		Formula x874 = x875.eq(x877);
		Formula x870 = x874.forSome(x871);
		Formula x866 = x870.forAll(x867);
		Variable x881 = Variable.unary("IMPORTED_n");
		Expression x883 = x634.join(notifications);
		Expression x882 = x883.intersection(x45);
		Decls x880 = x881.oneOf(x882);
		Expression x887 = x881.join(uids);
		Expression x886 = x887.join(x634);
		Formula x885 = x886.some();
		Variable x890 = Variable.unary("IMPORTED_p1");
		Expression x893 = x634.join(productions);
		Expression x894 = x634.join(notifications);
		Expression x892 = x893.union(x894);
		Expression x891 = x892.difference(x881);
		Decls x889 = x890.oneOf(x891);
		Expression x899 = x881.join(uids);
		Expression x898 = x899.join(x634);
		Expression x901 = x890.join(uids);
		Expression x900 = x901.join(x634);
		Expression x897 = x898.intersection(x900);
		Formula x896 = x897.some();
		Formula x895 = x896.not();
		Formula x888 = x895.forAll(x889);
		Formula x884 = x885.and(x888);
		Formula x879 = x884.forAll(x880);
		Formula x865 = x866.and(x879);
		Variable x904 = Variable.unary("IMPORTED_n");
		Expression x906 = x634.join(notifications);
		Expression x905 = x906.intersection(x46);
		Decls x903 = x904.oneOf(x905);
		Expression x911 = x904.join(uids);
		Expression x910 = x911.join(x634);
		Expression x915 = x634.join(productions);
		Expression x918 = x904.join(x62);
		Expression x917 = x60.join(x918);
		Expression x916 = x160.intersection(x917);
		Expression x914 = x915.intersection(x916);
		Expression x913 = x914.join(uids);
		Expression x912 = x913.join(x634);
		Expression x909 = x910.intersection(x912);
		Formula x908 = x909.some();
		Expression x922 = x904.join(uids);
		Expression x921 = x922.join(x634);
		Expression x926 = x634.join(productions);
		Expression x929 = x904.join(x62);
		Expression x928 = x60.join(x929);
		Expression x927 = x160.intersection(x928);
		Expression x925 = x926.intersection(x927);
		Expression x924 = x925.join(uids);
		Expression x923 = x924.join(x634);
		Formula x920 = x921.in(x923);
		Formula x919 = x920.not();
		Formula x907 = x908.and(x919);
		Formula x902 = x907.forAll(x903);
		Formula x864 = x865.and(x902);
		Formula x848 = x849.and(x864);
		Variable x933 = Variable.unary("IMPORTED_n");
		Expression x935 = x634.join(notifications);
		Expression x934 = x935.intersection(x45);
		Decls x932 = x933.oneOf(x934);
		Variable x938 = Variable.unary("IMPORTED_g");
		Expression x939 = x630.join(groups);
		Decls x937 = x938.oneOf(x939);
		Expression x943 = x938.join(uids);
		Expression x942 = x943.join(x630);
		Expression x945 = x933.join(uids);
		Expression x944 = x945.join(x634);
		Formula x941 = x942.eq(x944);
		Expression x947 = x933.join(x63);
		Expression x950 = x938.join(x58);
		Expression x952 = x72.closure();
		Expression x951 = x950.join(x952);
		Expression x949 = x950.difference(x951);
		Expression x948 = x949.join(x57);
		Formula x946 = x947.eq(x948);
		Formula x940 = x941.and(x946);
		Formula x936 = x940.forSome(x937);
		Formula x931 = x936.forAll(x932);
		Variable x956 = Variable.unary("IMPORTED_g");
		Expression x957 = x630.join(groups);
		Decls x955 = x956.oneOf(x957);
		Variable x959 = Variable.unary("IMPORTED_p1");
		Expression x960 = x634.join(productions);
		Decls x958 = x959.oneOf(x960);
		Decls x954 = x955.and(x958);
		Expression x967 = x956.join(uids);
		Expression x966 = x967.join(x630);
		Expression x969 = x959.join(uids);
		Expression x968 = x969.join(x634);
		Expression x965 = x966.intersection(x968);
		Formula x964 = x965.some();
		Expression x973 = x956.join(uids);
		Expression x972 = x973.join(x630);
		Expression x975 = x959.join(uids);
		Expression x974 = x975.join(x634);
		Formula x971 = x972.in(x974);
		Formula x970 = x971.not();
		Formula x963 = x964.and(x970);
		Formula x962 = x963.not();
		Variable x979 = Variable.unary("IMPORTED_n");
		Expression x981 = x634.join(notifications);
		Expression x980 = x981.intersection(x46);
		Decls x978 = x979.oneOf(x980);
		Expression x984 = x979.join(x62);
		Expression x985 = x959.join(x60);
		Formula x983 = x984.eq(x985);
		Expression x988 = x979.join(uids);
		Expression x987 = x988.join(x634);
		Expression x990 = x956.join(uids);
		Expression x989 = x990.join(x630);
		Formula x986 = x987.eq(x989);
		Formula x982 = x983.and(x986);
		Expression x977 = x982.comprehension(x978);
		Formula x976 = x977.one();
		Formula x961 = x962.or(x976);
		Formula x953 = x961.forAll(x954);
		Formula x930 = x931.and(x953);
		Formula x847 = x848.and(x930);
		Formula x829 = x830.and(x847);
		Formula x638 = x639.and(x829);
		Formula x637 = x638.not();
		Variable x995 = Variable.unary("same_ptcris_p1");
		Expression x996 = x632.join(productions);
		Decls x994 = x995.oneOf(x996);
		Variable x999 = Variable.unary("same_ptcris_p2");
		Expression x1000 = x634.join(productions);
		Decls x998 = x999.oneOf(x1000);
		Expression x1003 = x995.join(x60);
		Expression x1004 = x999.join(x60);
		Formula x1002 = x1003.eq(x1004);
		Expression x1007 = x995.join(x61);
		Expression x1008 = x999.join(x61);
		Formula x1006 = x1007.eq(x1008);
		Expression x1011 = x995.join(uids);
		Expression x1010 = x1011.join(x632);
		Expression x1013 = x999.join(uids);
		Expression x1012 = x1013.join(x634);
		Formula x1009 = x1010.eq(x1012);
		Formula x1005 = x1006.and(x1009);
		Formula x1001 = x1002.and(x1005);
		Formula x997 = x1001.forSome(x998);
		Formula x993 = x997.forAll(x994);
		Variable x1018 = Variable.unary("same_ptcris_p2");
		Expression x1019 = x634.join(productions);
		Decls x1017 = x1018.oneOf(x1019);
		Variable x1022 = Variable.unary("same_ptcris_p1");
		Expression x1023 = x632.join(productions);
		Decls x1021 = x1022.oneOf(x1023);
		Expression x1026 = x1022.join(x60);
		Expression x1027 = x1018.join(x60);
		Formula x1025 = x1026.eq(x1027);
		Expression x1030 = x1022.join(x61);
		Expression x1031 = x1018.join(x61);
		Formula x1029 = x1030.eq(x1031);
		Expression x1034 = x1022.join(uids);
		Expression x1033 = x1034.join(x632);
		Expression x1036 = x1018.join(uids);
		Expression x1035 = x1036.join(x634);
		Formula x1032 = x1033.eq(x1035);
		Formula x1028 = x1029.and(x1032);
		Formula x1024 = x1025.and(x1028);
		Formula x1020 = x1024.forSome(x1021);
		Formula x1016 = x1020.forAll(x1017);
		Variable x1039 = Variable.unary("same_ptcris_n1");
		Expression x1041 = x632.join(notifications);
		Expression x1040 = x1041.intersection(x46);
		Decls x1038 = x1039.oneOf(x1040);
		Variable x1044 = Variable.unary("same_ptcris_n2");
		Expression x1046 = x634.join(notifications);
		Expression x1045 = x1046.intersection(x46);
		Decls x1043 = x1044.oneOf(x1045);
		Expression x1049 = x1039.join(x62);
		Expression x1050 = x1044.join(x62);
		Formula x1048 = x1049.eq(x1050);
		Expression x1053 = x1039.join(uids);
		Expression x1052 = x1053.join(x632);
		Expression x1055 = x1044.join(uids);
		Expression x1054 = x1055.join(x634);
		Formula x1051 = x1052.eq(x1054);
		Formula x1047 = x1048.and(x1051);
		Formula x1042 = x1047.forSome(x1043);
		Formula x1037 = x1042.forAll(x1038);
		Formula x1015 = x1016.and(x1037);
		Variable x1058 = Variable.unary("same_ptcris_n2");
		Expression x1060 = x634.join(notifications);
		Expression x1059 = x1060.intersection(x46);
		Decls x1057 = x1058.oneOf(x1059);
		Variable x1063 = Variable.unary("same_ptcris_n1");
		Expression x1065 = x632.join(notifications);
		Expression x1064 = x1065.intersection(x46);
		Decls x1062 = x1063.oneOf(x1064);
		Expression x1068 = x1063.join(x62);
		Expression x1069 = x1058.join(x62);
		Formula x1067 = x1068.eq(x1069);
		Expression x1072 = x1063.join(uids);
		Expression x1071 = x1072.join(x632);
		Expression x1074 = x1058.join(uids);
		Expression x1073 = x1074.join(x634);
		Formula x1070 = x1071.eq(x1073);
		Formula x1066 = x1067.and(x1070);
		Formula x1061 = x1066.forSome(x1062);
		Formula x1056 = x1061.forAll(x1057);
		Formula x1014 = x1015.and(x1056);
		Formula x992 = x993.and(x1014);
		Expression x1079 = x632.join(exported);
		Expression x1078 = x1079.join(x60);
		Expression x1081 = x634.join(exported);
		Expression x1080 = x1081.join(x60);
		Formula x1077 = x1078.eq(x1080);
		Variable x1084 = Variable.unary("same_ptcris_n1");
		Expression x1086 = x632.join(notifications);
		Expression x1085 = x1086.intersection(x45);
		Decls x1083 = x1084.oneOf(x1085);
		Variable x1089 = Variable.unary("same_ptcris_n2");
		Expression x1091 = x634.join(notifications);
		Expression x1090 = x1091.intersection(x45);
		Decls x1088 = x1089.oneOf(x1090);
		Expression x1095 = x1084.join(x63);
		Expression x1096 = x1089.join(x63);
		Formula x1094 = x1095.eq(x1096);
		Expression x1099 = x1084.join(uids);
		Expression x1098 = x1099.join(x632);
		Expression x1101 = x1089.join(uids);
		Expression x1100 = x1101.join(x634);
		Formula x1097 = x1098.eq(x1100);
		Formula x1093 = x1094.and(x1097);
		Variable x1108 = Variable.unary("identical_creations_n1");
		Expression x1110 = x632.join(notifications);
		Expression x1109 = x1110.intersection(x45);
		Decls x1107 = x1108.oneOf(x1109);
		Variable x1112 = Variable.unary("identical_creations_n2");
		Decls x1111 = x1112.oneOf(x1109);
		Decls x1106 = x1107.and(x1111);
		Expression x1115 = x1108.join(x63);
		Expression x1116 = x1112.join(x63);
		Formula x1114 = x1115.eq(x1116);
		Expression x1119 = x1108.join(uids);
		Expression x1118 = x1119.join(x632);
		Expression x1121 = x1112.join(uids);
		Expression x1120 = x1121.join(x632);
		Formula x1117 = x1118.eq(x1120);
		Formula x1113 = x1114.and(x1117);
		Expression x1105 = x1113.comprehension(x1106);
		Expression x1104 = x1084.join(x1105);
		IntExpression x1103 = x1104.count();
		Variable x1127 = Variable.unary("identical_creations_n1");
		Expression x1129 = x634.join(notifications);
		Expression x1128 = x1129.intersection(x45);
		Decls x1126 = x1127.oneOf(x1128);
		Variable x1131 = Variable.unary("identical_creations_n2");
		Decls x1130 = x1131.oneOf(x1128);
		Decls x1125 = x1126.and(x1130);
		Expression x1134 = x1127.join(x63);
		Expression x1135 = x1131.join(x63);
		Formula x1133 = x1134.eq(x1135);
		Expression x1138 = x1127.join(uids);
		Expression x1137 = x1138.join(x634);
		Expression x1140 = x1131.join(uids);
		Expression x1139 = x1140.join(x634);
		Formula x1136 = x1137.eq(x1139);
		Formula x1132 = x1133.and(x1136);
		Expression x1124 = x1132.comprehension(x1125);
		Expression x1123 = x1089.join(x1124);
		IntExpression x1122 = x1123.count();
		Formula x1102 = x1103.eq(x1122);
		Formula x1092 = x1093.and(x1102);
		Formula x1087 = x1092.forSome(x1088);
		Formula x1082 = x1087.forAll(x1083);
		Formula x1076 = x1077.and(x1082);
		Variable x1143 = Variable.unary("same_ptcris_n1");
		Expression x1145 = x634.join(notifications);
		Expression x1144 = x1145.intersection(x45);
		Decls x1142 = x1143.oneOf(x1144);
		Variable x1148 = Variable.unary("same_ptcris_n2");
		Expression x1150 = x632.join(notifications);
		Expression x1149 = x1150.intersection(x45);
		Decls x1147 = x1148.oneOf(x1149);
		Expression x1154 = x1143.join(x63);
		Expression x1155 = x1148.join(x63);
		Formula x1153 = x1154.eq(x1155);
		Expression x1158 = x1143.join(uids);
		Expression x1157 = x1158.join(x634);
		Expression x1160 = x1148.join(uids);
		Expression x1159 = x1160.join(x632);
		Formula x1156 = x1157.eq(x1159);
		Formula x1152 = x1153.and(x1156);
		Variable x1167 = Variable.unary("identical_creations_n1");
		Expression x1169 = x634.join(notifications);
		Expression x1168 = x1169.intersection(x45);
		Decls x1166 = x1167.oneOf(x1168);
		Variable x1171 = Variable.unary("identical_creations_n2");
		Decls x1170 = x1171.oneOf(x1168);
		Decls x1165 = x1166.and(x1170);
		Expression x1174 = x1167.join(x63);
		Expression x1175 = x1171.join(x63);
		Formula x1173 = x1174.eq(x1175);
		Expression x1178 = x1167.join(uids);
		Expression x1177 = x1178.join(x634);
		Expression x1180 = x1171.join(uids);
		Expression x1179 = x1180.join(x634);
		Formula x1176 = x1177.eq(x1179);
		Formula x1172 = x1173.and(x1176);
		Expression x1164 = x1172.comprehension(x1165);
		Expression x1163 = x1143.join(x1164);
		IntExpression x1162 = x1163.count();
		Variable x1186 = Variable.unary("identical_creations_n1");
		Expression x1188 = x632.join(notifications);
		Expression x1187 = x1188.intersection(x45);
		Decls x1185 = x1186.oneOf(x1187);
		Variable x1190 = Variable.unary("identical_creations_n2");
		Decls x1189 = x1190.oneOf(x1187);
		Decls x1184 = x1185.and(x1189);
		Expression x1193 = x1186.join(x63);
		Expression x1194 = x1190.join(x63);
		Formula x1192 = x1193.eq(x1194);
		Expression x1197 = x1186.join(uids);
		Expression x1196 = x1197.join(x632);
		Expression x1199 = x1190.join(uids);
		Expression x1198 = x1199.join(x632);
		Formula x1195 = x1196.eq(x1198);
		Formula x1191 = x1192.and(x1195);
		Expression x1183 = x1191.comprehension(x1184);
		Expression x1182 = x1148.join(x1183);
		IntExpression x1181 = x1182.count();
		Formula x1161 = x1162.eq(x1181);
		Formula x1151 = x1152.and(x1161);
		Formula x1146 = x1151.forSome(x1147);
		Formula x1141 = x1146.forAll(x1142);
		Formula x1075 = x1076.and(x1141);
		Formula x991 = x992.and(x1075);
		Formula x636 = x637.or(x991);
		Formula x627 = x636.forAll(x628);
		Formula x626 = x627.not();
		return x626;
	}

	private static Formula f2() {
		Variable x617 = Variable.unary("hippocratic_import_p");
		Decls x616 = x617.oneOf(ptcris);
		Variable x620 = Variable.unary("hippocratic_import_n");
		Expression x622 = x617.join(notifications);
		Expression x621 = x622.intersection(x46);
		Decls x619 = x620.oneOf(x621);
		Expression x625 = x620.join(uids);
		Expression x624 = x625.join(x617);
		Formula x623 = x624.some();
		Formula x618 = x623.forAll(x619);
		Formula x615 = x618.forAll(x616);
		return x615;
	}

	private static Formula f3() {
		Variable x605 = Variable.unary("hippocratic_import_p");
		Decls x604 = x605.oneOf(ptcris);
		Variable x608 = Variable.unary("hippocratic_import_n");
		Expression x610 = x605.join(notifications);
		Expression x609 = x610.intersection(x46);
		Decls x607 = x608.oneOf(x609);
		Expression x612 = x608.join(x62);
		Expression x614 = x605.join(productions);
		Expression x613 = x614.join(x60);
		Formula x611 = x612.in(x613);
		Formula x606 = x611.forAll(x607);
		Formula x603 = x606.forAll(x604);
		return x603;
	}

	private static Formula f4() {
		Variable x592 = Variable.unary("hippocratic_import_p");
		Decls x591 = x592.oneOf(ptcris);
		Variable x595 = Variable.unary("hippocratic_import_n");
		Expression x597 = x592.join(notifications);
		Expression x596 = x597.intersection(x45);
		Decls x594 = x595.oneOf(x596);
		Expression x600 = x595.join(x62);
		Expression x602 = x592.join(productions);
		Expression x601 = x602.join(x60);
		Formula x599 = x600.in(x601);
		Formula x598 = x599.not();
		Formula x593 = x598.forAll(x594);
		Formula x590 = x593.forAll(x591);
		return x590;
	}

	private static Formula f5() {
		Variable x574 = Variable.unary("hippocratic_import_p");
		Decls x573 = x574.oneOf(ptcris);
		Variable x578 = Variable.unary("hippocratic_import_n1");
		Expression x580 = x574.join(notifications);
		Expression x579 = x580.intersection(x45);
		Decls x577 = x578.oneOf(x579);
		Variable x582 = Variable.unary("hippocratic_import_n2");
		Decls x581 = x582.oneOf(x579);
		Decls x576 = x577.and(x581);
		Expression x586 = x578.intersection(x582);
		Formula x585 = x586.no();
		Expression x588 = x578.join(x62);
		Expression x589 = x582.join(x62);
		Formula x587 = x588.eq(x589);
		Formula x584 = x585.and(x587);
		Formula x583 = x584.not();
		Formula x575 = x583.forAll(x576);
		Formula x572 = x575.forAll(x573);
		return x572;
	}

	private static Formula f6() {
		Variable x545 = Variable.unary("hippocratic_import_p");
		Decls x544 = x545.oneOf(ptcris);
		Variable x549 = Variable.unary("hippocratic_import_p1");
		Expression x550 = x545.join(productions);
		Decls x548 = x549.oneOf(x550);
		Variable x552 = Variable.unary("hippocratic_import_p2");
		Decls x551 = x552.oneOf(x550);
		Decls x547 = x548.and(x551);
		Expression x556 = x549.intersection(x552);
		Formula x555 = x556.no();
		Formula x554 = x555.not();
		Expression x563 = x549.join(uids);
		Expression x562 = x563.join(x545);
		Expression x565 = x552.join(uids);
		Expression x564 = x565.join(x545);
		Expression x561 = x562.intersection(x564);
		Formula x560 = x561.some();
		Formula x559 = x560.not();
		Expression x568 = x545.join(exported);
		Formula x567 = x549.in(x568);
		Formula x566 = x567.not();
		Formula x558 = x559.or(x566);
		Expression x571 = x545.join(exported);
		Formula x570 = x552.in(x571);
		Formula x569 = x570.not();
		Formula x557 = x558.or(x569);
		Formula x553 = x554.or(x557);
		Formula x546 = x553.forAll(x547);
		Formula x543 = x546.forAll(x544);
		return x543;
	}

	private static Formula f7() {
		Variable x535 = Variable.unary("hippocratic_import_p");
		Decls x534 = x535.oneOf(ptcris);
		Variable x538 = Variable.unary("hippocratic_import_e");
		Expression x539 = x535.join(exported);
		Decls x537 = x538.oneOf(x539);
		Expression x542 = x538.join(uids);
		Expression x541 = x542.join(x535);
		Formula x540 = x541.some();
		Formula x536 = x540.forAll(x537);
		Formula x533 = x536.forAll(x534);
		return x533;
	}

	private static Formula f8() {
		Variable x518 = Variable.unary("hippocratic_import_p");
		Decls x517 = x518.oneOf(ptcris);
		Variable x522 = Variable.unary("hippocratic_import_p1");
		Expression x523 = x518.join(productions);
		Decls x521 = x522.oneOf(x523);
		Variable x525 = Variable.unary("hippocratic_import_p2");
		Decls x524 = x525.oneOf(x523);
		Decls x520 = x521.and(x524);
		Expression x529 = x522.intersection(x525);
		Formula x528 = x529.no();
		Expression x531 = x522.join(x60);
		Expression x532 = x525.join(x60);
		Formula x530 = x531.eq(x532);
		Formula x527 = x528.and(x530);
		Formula x526 = x527.not();
		Formula x519 = x526.forAll(x520);
		Formula x516 = x519.forAll(x517);
		return x516;
	}

	private static Formula f9() {
		Variable x492 = Variable.unary("hippocratic_import_o");
		Decls x491 = x492.oneOf(orcid);
		Variable x496 = Variable.unary("hippocratic_import_w1");
		Expression x498 = x492.join(groups);
		Expression x497 = x498.join(x58);
		Decls x495 = x496.oneOf(x497);
		Variable x500 = Variable.unary("hippocratic_import_w2");
		Decls x499 = x500.oneOf(x497);
		Decls x494 = x495.and(x499);
		Expression x504 = x496.intersection(x500);
		Formula x503 = x504.no();
		Formula x502 = x503.not();
		Expression x508 = x496.join(x56);
		Expression x509 = x500.join(x56);
		Formula x507 = x508.eq(x509);
		Formula x506 = x507.not();
		Expression x513 = x496.join(uids);
		Expression x512 = x513.join(x492);
		Expression x515 = x500.join(uids);
		Expression x514 = x515.join(x492);
		Expression x511 = x512.intersection(x514);
		Formula x510 = x511.no();
		Formula x505 = x506.or(x510);
		Formula x501 = x502.or(x505);
		Formula x493 = x501.forAll(x494);
		Formula x490 = x493.forAll(x491);
		return x490;
	}

	private static Formula f10() {
		Variable x474 = Variable.unary("hippocratic_import_o");
		Decls x473 = x474.oneOf(orcid);
		Variable x478 = Variable.unary("hippocratic_import_w1");
		Expression x480 = x474.join(groups);
		Expression x479 = x480.join(x58);
		Decls x477 = x478.oneOf(x479);
		Variable x482 = Variable.unary("hippocratic_import_w2");
		Decls x481 = x482.oneOf(x479);
		Decls x476 = x477.and(x481);
		Expression x486 = x478.intersection(x482);
		Formula x485 = x486.no();
		Expression x488 = x478.join(x55);
		Expression x489 = x482.join(x55);
		Formula x487 = x488.eq(x489);
		Formula x484 = x485.and(x487);
		Formula x483 = x484.not();
		Formula x475 = x483.forAll(x476);
		Formula x472 = x475.forAll(x473);
		return x472;
	}

	private static Formula f11() {
		Expression x82 = x3.union(x4);
		Expression x87 = x7.union(x8);
		Expression x90 = x87.union(x9);
		Expression x93 = x90.union(x10);
		Expression x98 = x13.union(x14);
		Expression x101 = x98.union(x15);
		Expression x104 = x101.union(x16);
		Expression x107 = x104.union(x17);
		Expression x110 = x107.union(x18);
		Expression x115 = x21.union(x22);
		Expression x118 = x115.union(x23);
		Expression x123 = x26.union(x27);
		Expression x205 = x123.union(x28);
		Expression x128 = x29.union(x30);

		Expression x131 = x128.union(x31);
		Expression x134 = x131.union(x32);

		Expression x139 = x35.union(x36);
		Expression x142 = x139.union(x37);
		Expression x145 = x142.union(x38);

		Expression x149 = x134.union(x33);
		Expression x148 = x149.union(x34);
		Expression x151 = x145.union(x39);
		Expression x150 = x151.union(x40);

		Expression x156 = x41.union(x42);

		Expression x159 = x148.union(x150);
		Expression x161 = x156.union(x43);
		Expression x160 = x161.union(x44);
		Expression x166 = x159.union(x160);
		Expression x167 = x45.union(x46);

		Expression x194 = x93.union(x11);
		Expression x193 = x194.union(x12);
		Expression x216 = x118.union(x24);
		Expression x215 = x216.union(x25);
		Expression x281 = x166.union(x167);
		Expression x286 = x110.union(x19);
		Expression x285 = x286.union(x20);
		Expression x287 = orcid.union(ptcris);
		Expression x248 = x82.union(x5);
		Expression x247 = x248.union(x6);

		Variable x424 = Variable.unary("hippocratic_import_o");
		Decls x423 = x424.oneOf(orcid);
		Variable x426 = Variable.unary("hippocratic_import_w");
		Expression x428 = x424.join(groups);
		Expression x427 = x428.join(x58);
		Decls x425 = x426.oneOf(x427);
		Decls x422 = x423.and(x425);
		Expression x432 = x424.join(groups);
		Expression x433 = x58.join(x426);
		Expression x431 = x432.intersection(x433);
		Formula x430 = x431.one();
		Variable x441 = Variable.unary("similar_w1");
		Expression x443 = x424.join(groups);
		Expression x442 = x443.join(x58);
		Decls x440 = x441.oneOf(x442);
		Variable x445 = Variable.unary("similar_w2");
		Decls x444 = x445.oneOf(x442);
		Decls x439 = x440.and(x444);
		Expression x449 = x441.join(uids);
		Expression x448 = x449.join(x424);
		Expression x451 = x445.join(uids);
		Expression x450 = x451.join(x424);
		Expression x447 = x448.intersection(x450);
		Formula x446 = x447.some();
		Expression x438 = x446.comprehension(x439);
		Expression x437 = x438.closure();
		Expression x466 = Expression.INTS.union(x2);
		Expression x465 = x466.union(x247);
		Expression x464 = x465.union(x193);
		Expression x463 = x464.union(x285);
		Expression x462 = x463.union(x215);
		Expression x461 = x462.union(x205);
		Expression x460 = x461.union(x281);
		Expression x459 = x460.union(x287);
		Expression x458 = x459.union(x49);
		Expression x457 = x458.union(x50);
		Expression x456 = x457.union(x51);
		Expression x455 = x456.union(x52);
		Expression x454 = x455.product(Expression.UNIV);
		Expression x452 = Expression.IDEN.intersection(x454);
		Expression x436 = x437.union(x452);
		Expression x435 = x426.join(x436);
		Expression x470 = x424.join(groups);
		Expression x471 = x58.join(x426);
		Expression x469 = x470.intersection(x471);
		Expression x468 = x469.join(x58);
		Formula x434 = x435.eq(x468);
		Formula x429 = x430.and(x434);
		Formula x421 = x429.forAll(x422);
		return x421;
	}

	private static Formula f12() {
		Expression x98 = x13.union(x14);
		Expression x101 = x98.union(x15);
		Expression x104 = x101.union(x16);
		Expression x107 = x104.union(x17);
		Expression x110 = x107.union(x18);
		Expression x128 = x29.union(x30);

		Expression x131 = x128.union(x31);
		Expression x134 = x131.union(x32);

		Expression x139 = x35.union(x36);
		Expression x142 = x139.union(x37);
		Expression x145 = x142.union(x38);

		Expression x149 = x134.union(x33);
		Expression x148 = x149.union(x34);
		Expression x151 = x145.union(x39);
		Expression x150 = x151.union(x40);

		Expression x156 = x41.union(x42);
		Expression x159 = x148.union(x150);
		Expression x161 = x156.union(x43);
		Expression x160 = x161.union(x44);
		Expression x166 = x159.union(x160);
		Expression x167 = x45.union(x46);

		Variable x280 = Variable.unary("hippocratic_import_this");
		Expression x281 = x166.union(x167);
		Decls x279 = x280.oneOf(x281);
		Expression x283 = x280.join(uids);
		Expression x286 = x110.union(x19);
		Expression x285 = x286.union(x20);
		Expression x287 = orcid.union(ptcris);
		Expression x284 = x285.product(x287);
		Formula x282 = x283.in(x284);
		Formula x278 = x282.forAll(x279);

		Expression x290 = uids.join(Expression.UNIV);
		Expression x289 = x290.join(Expression.UNIV);
		Formula x288 = x289.in(x281);

		Variable x293 = Variable.unary("hippocratic_import_this");
		Decls x292 = x293.oneOf(orcid);
		Expression x295 = x293.join(groups);
		Formula x294 = x295.in(x150);
		Formula x291 = x294.forAll(x292);

		Expression x297 = groups.join(Expression.UNIV);
		Formula x296 = x297.in(orcid);

		Variable x300 = Variable.unary("hippocratic_import_this");
		Decls x299 = x300.oneOf(orcid);
		Expression x302 = x300.join(outputs);
		Expression x303 = x300.join(groups);
		Formula x301 = x302.eq(x303);
		Formula x298 = x301.forAll(x299);

		Variable x306 = Variable.unary("hippocratic_import_this");
		Decls x305 = x306.oneOf(ptcris);
		Expression x308 = x306.join(productions);
		Formula x307 = x308.in(x160);
		Formula x304 = x307.forAll(x305);

		Expression x310 = productions.join(Expression.UNIV);
		Formula x309 = x310.in(ptcris);

		Variable x313 = Variable.unary("hippocratic_import_this");
		Decls x312 = x313.oneOf(ptcris);
		Expression x315 = x313.join(exported);
		Expression x316 = x313.join(productions);
		Formula x314 = x315.in(x316);
		Formula x311 = x314.forAll(x312);

		Expression x318 = exported.join(Expression.UNIV);
		Formula x317 = x318.in(ptcris);

		Variable x321 = Variable.unary("hippocratic_import_this");
		Decls x320 = x321.oneOf(ptcris);
		Expression x323 = x321.join(notifications);
		Formula x322 = x323.in(x167);
		Formula x319 = x322.forAll(x320);

		Expression x325 = notifications.join(Expression.UNIV);
		Formula x324 = x325.in(ptcris);

		Variable x328 = Variable.unary("hippocratic_import_this");
		Decls x327 = x328.oneOf(ptcris);
		Expression x330 = x328.join(outputs);
		Expression x331 = x328.join(productions);
		Formula x329 = x330.eq(x331);
		Formula x326 = x329.forAll(x327);

		Variable x334 = Variable.unary("hippocratic_import_this");
		Decls x333 = x334.oneOf(x287);
		Expression x336 = x334.join(outputs);
		Formula x335 = x336.in(x281);
		Formula x332 = x335.forAll(x333);

		Expression x338 = outputs.join(Expression.UNIV);
		Formula x337 = x338.in(x287);

		Expression x341 = x49.product(x67);
		Expression x340 = x49.join(x341);
		Formula x339 = x340.in(orcid);

		Expression x344 = x49.product(x68);
		Expression x343 = x49.join(x344);
		Expression x345 = orcid.product(orcid);
		Formula x342 = x343.in(x345);

		Formula x346 = x68.totalOrder(orcid, x67, x75);

		Expression x349 = x50.product(x69);
		Expression x348 = x50.join(x349);
		Formula x347 = x348.in(ptcris);

		Expression x352 = x50.product(x70);
		Expression x351 = x50.join(x352);
		Expression x353 = ptcris.product(ptcris);
		Formula x350 = x351.in(x353);

		Formula x354 = x70.totalOrder(ptcris, x69, x76);

		return Formula.compose(FormulaOperator.AND, x278, x288, x291, x296, x298, x304, x309, x311, x317, x319, x324,
				x326, x332, x337, x339, x342, x346, x347, x350, x354);
	}

	private static Formula b2() {

		Expression x123 = x26.union(x27);
		Expression x205 = x123.union(x28);

		Variable x397 = Variable.unary("v7");
		Decls x396 = x397.oneOf(x205);
		Expression x402 = x52.join(x73);
		Formula x401 = x397.eq(x402);
		Expression x405 = x52.join(x74);
		Expression x404 = x405.join(x397);
		Formula x403 = x404.one();
		Formula x400 = x401.or(x403);
		Expression x409 = x405.join(x205);
		Expression x408 = x205.difference(x409);
		Formula x407 = x397.eq(x408);
		Expression x411 = x397.join(x405);
		Formula x410 = x411.one();
		Formula x406 = x407.or(x410);
		Formula x399 = x400.and(x406);
		Expression x415 = x405.closure();
		Expression x414 = x397.join(x415);
		Formula x413 = x397.in(x414);
		Formula x412 = x413.not();
		Formula x398 = x399.and(x412);
		Formula x395 = x398.forAll(x396);
		Expression x418 = x405.reflexiveClosure();
		Expression x417 = x402.join(x418);
		Formula x416 = x205.in(x417);
		Formula x394 = x395.and(x416);
		Expression x420 = x405.join(x402);
		Formula x419 = x420.no();
		Formula x393 = x394.and(x419);
		return x393;
	}

	private static Formula b1() {
		Expression x128 = x29.union(x30);

		Expression x131 = x128.union(x31);
		Expression x134 = x131.union(x32);

		Expression x149 = x134.union(x33);
		Expression x148 = x149.union(x34);
		Expression x123 = x26.union(x27);
		Expression x205 = x123.union(x28);

		Expression x357 = x51.product(x71);
		Expression x356 = x51.join(x357);
		Formula x355 = x356.in(x148);
		Expression x360 = x51.product(x72);
		Expression x359 = x51.join(x360);
		Expression x361 = x148.product(x148);
		Formula x358 = x359.in(x361);
		Variable x366 = Variable.unary("v6");
		Decls x365 = x366.oneOf(x148);
		Formula x370 = x366.eq(x71);
		Expression x372 = x72.join(x366);
		Formula x371 = x372.one();
		Formula x369 = x370.or(x371);
		Expression x376 = x72.join(x148);
		Expression x375 = x148.difference(x376);
		Formula x374 = x366.eq(x375);
		Expression x378 = x366.join(x72);
		Formula x377 = x378.one();
		Formula x373 = x374.or(x377);
		Formula x368 = x369.and(x373);
		Expression x382 = x72.closure();
		Expression x381 = x366.join(x382);
		Formula x380 = x366.in(x381);
		Formula x379 = x380.not();
		Formula x367 = x368.and(x379);
		Formula x364 = x367.forAll(x365);
		Expression x385 = x72.reflexiveClosure();
		Expression x384 = x71.join(x385);
		Formula x383 = x148.in(x384);
		Formula x363 = x364.and(x383);
		Expression x387 = x72.join(x71);
		Formula x386 = x387.no();
		Formula x362 = x363.and(x386);
		Expression x389 = x52.join(x73);
		Formula x388 = x389.in(x205);
		Expression x391 = x52.join(x74);
		Expression x392 = x205.product(x205);
		Formula x390 = x391.in(x392);
		return x355.and(x358).and(x362).and(x388).and(x390);
	}

	private static Formula b3() {
		Expression x82 = x3.union(x4);
		Expression x115 = x21.union(x22);
		Expression x118 = x115.union(x23);

		Expression x156 = x41.union(x42);
		Expression x161 = x156.union(x43);
		Expression x160 = x161.union(x44);
		Expression x167 = x45.union(x46);

		Expression x216 = x118.union(x24);
		Expression x215 = x216.union(x25);

		Variable x242 = Variable.unary("hippocratic_import_this");
		Decls x241 = x242.oneOf(x160);
		Expression x245 = x242.join(x60);
		Formula x244 = x245.one();
		Expression x248 = x82.union(x5);
		Expression x247 = x248.union(x6);
		Formula x246 = x245.in(x247);
		Formula x243 = x244.and(x246);
		Formula x240 = x243.forAll(x241);

		Expression x250 = x60.join(Expression.UNIV);
		Formula x249 = x250.in(x160);

		Variable x253 = Variable.unary("hippocratic_import_this");
		Decls x252 = x253.oneOf(x160);
		Expression x256 = x253.join(x61);
		Formula x255 = x256.one();
		Formula x257 = x256.in(x215);
		Formula x254 = x255.and(x257);
		Formula x251 = x254.forAll(x252);

		Expression x259 = x61.join(Expression.UNIV);
		Formula x258 = x259.in(x160);

		Variable x262 = Variable.unary("hippocratic_import_this");
		Decls x261 = x262.oneOf(x45);
		Expression x265 = x262.join(x63);
		Formula x264 = x265.one();
		Formula x266 = x265.in(x215);
		Formula x263 = x264.and(x266);
		Formula x260 = x263.forAll(x261);

		Expression x268 = x63.join(Expression.UNIV);
		Formula x267 = x268.in(x45);

		Variable x271 = Variable.unary("hippocratic_import_this");
		Decls x270 = x271.oneOf(x167);
		Expression x274 = x271.join(x62);
		Formula x273 = x274.one();
		Formula x275 = x274.in(x247);
		Formula x272 = x273.and(x275);
		Formula x269 = x272.forAll(x270);

		Expression x277 = x62.join(Expression.UNIV);
		Formula x276 = x277.in(x167);

		return Formula.compose(FormulaOperator.AND, x240, x249, x251, x258, x260, x267, x269, x276);
	}

	private static Formula b0() {
		Expression x79 = x3.intersection(x4);
		Formula x78 = x79.no();

		Expression x82 = x3.union(x4);
		Expression x81 = x82.intersection(x5);
		Formula x80 = x81.no();

		Expression x84 = x7.intersection(x8);
		Formula x83 = x84.no();

		Expression x87 = x7.union(x8);
		Expression x86 = x87.intersection(x9);
		Formula x85 = x86.no();

		Expression x90 = x87.union(x9);
		Expression x89 = x90.intersection(x10);
		Formula x88 = x89.no();

		Expression x93 = x90.union(x10);
		Expression x92 = x93.intersection(x11);
		Formula x91 = x92.no();

		Expression x95 = x13.intersection(x14);
		Formula x94 = x95.no();

		Expression x98 = x13.union(x14);
		Expression x97 = x98.intersection(x15);
		Formula x96 = x97.no();

		Expression x101 = x98.union(x15);
		Expression x100 = x101.intersection(x16);
		Formula x99 = x100.no();

		Expression x104 = x101.union(x16);
		Expression x103 = x104.intersection(x17);
		Formula x102 = x103.no();

		Expression x107 = x104.union(x17);
		Expression x106 = x107.intersection(x18);
		Formula x105 = x106.no();

		Expression x110 = x107.union(x18);
		Expression x109 = x110.intersection(x19);
		Formula x108 = x109.no();

		Expression x112 = x21.intersection(x22);
		Formula x111 = x112.no();

		Expression x115 = x21.union(x22);
		Expression x114 = x115.intersection(x23);
		Formula x113 = x114.no();

		Expression x118 = x115.union(x23);
		Expression x117 = x118.intersection(x24);
		Formula x116 = x117.no();

		Expression x120 = x26.intersection(x27);
		Formula x119 = x120.no();

		Expression x123 = x26.union(x27);
		Expression x122 = x123.intersection(x28);
		Formula x121 = x122.no();

		Expression x125 = x29.intersection(x30);
		Formula x124 = x125.no();

		Expression x128 = x29.union(x30);
		Expression x127 = x128.intersection(x31);
		Formula x126 = x127.no();

		Expression x131 = x128.union(x31);
		Expression x130 = x131.intersection(x32);
		Formula x129 = x130.no();

		Expression x134 = x131.union(x32);
		Expression x133 = x134.intersection(x33);
		Formula x132 = x133.no();

		Expression x136 = x35.intersection(x36);
		Formula x135 = x136.no();

		Expression x139 = x35.union(x36);
		Expression x138 = x139.intersection(x37);
		Formula x137 = x138.no();

		Expression x142 = x139.union(x37);
		Expression x141 = x142.intersection(x38);
		Formula x140 = x141.no();

		Expression x145 = x142.union(x38);
		Expression x144 = x145.intersection(x39);
		Formula x143 = x144.no();

		Expression x149 = x134.union(x33);
		Expression x148 = x149.union(x34);
		Expression x151 = x145.union(x39);
		Expression x150 = x151.union(x40);
		Expression x147 = x148.intersection(x150);
		Formula x146 = x147.no();

		Expression x153 = x41.intersection(x42);
		Formula x152 = x153.no();

		Expression x156 = x41.union(x42);
		Expression x155 = x156.intersection(x43);
		Formula x154 = x155.no();

		Expression x159 = x148.union(x150);
		Expression x161 = x156.union(x43);
		Expression x160 = x161.union(x44);
		Expression x158 = x159.intersection(x160);
		Formula x157 = x158.no();

		Expression x163 = x45.intersection(x46);
		Formula x162 = x163.no();

		Expression x166 = x159.union(x160);
		Expression x167 = x45.union(x46);
		Expression x165 = x166.intersection(x167);
		Formula x164 = x165.no();

		Formula x171 = x160.no();
		Variable x175 = Variable.unary("v5");
		Decls x174 = x175.oneOf(x160);
		Variable x177 = Variable.unary("v4");
		Decls x176 = x177.oneOf(x160);
		Variable x179 = Variable.unary("v3");
		Decls x178 = x179.oneOf(x160);
		Variable x181 = Variable.unary("v2");
		Decls x180 = x181.oneOf(x160);
		Decls x173 = x174.and(x176).and(x178).and(x180);
		Expression x185 = x179.union(x181);
		Expression x184 = x177.union(x185);
		Expression x183 = x175.union(x184);
		Formula x182 = x183.eq(x160);
		Formula x172 = x182.forSome(x173);
		Formula x170 = x171.or(x172);

		Variable x188 = Variable.unary("hippocratic_import_this");
		Decls x187 = x188.oneOf(x148);
		Expression x191 = x188.join(x55);
		Formula x190 = x191.one();
		Expression x194 = x93.union(x11);
		Expression x193 = x194.union(x12);
		Formula x192 = x191.in(x193);
		Formula x189 = x190.and(x192);
		Formula x186 = x189.forAll(x187);

		Expression x196 = x55.join(Expression.UNIV);
		Formula x195 = x196.in(x148);

		Variable x200 = Variable.unary("hippocratic_import_this");
		Decls x199 = x200.oneOf(x148);
		Expression x203 = x200.join(x56);
		Formula x202 = x203.one();
		Expression x205 = x123.union(x28);
		Formula x204 = x203.in(x205);
		Formula x201 = x202.and(x204);
		Formula x198 = x201.forAll(x199);

		Expression x207 = x56.join(Expression.UNIV);
		Formula x206 = x207.in(x148);

		Variable x210 = Variable.unary("hippocratic_import_this");
		Decls x209 = x210.oneOf(x148);
		Expression x213 = x210.join(x57);
		Formula x212 = x213.one();
		Expression x216 = x118.union(x24);
		Expression x215 = x216.union(x25);
		Formula x214 = x213.in(x215);
		Formula x211 = x212.and(x214);
		Formula x208 = x211.forAll(x209);

		Expression x218 = x57.join(Expression.UNIV);
		Formula x217 = x218.in(x148);

		Variable x221 = Variable.unary("hippocratic_import_this");
		Decls x220 = x221.oneOf(x150);
		Expression x224 = x221.join(x58);
		Formula x223 = x224.some();
		Formula x225 = x224.in(x148);
		Formula x222 = x223.and(x225);
		Formula x219 = x222.forAll(x220);

		Expression x227 = x58.join(Expression.UNIV);
		Formula x226 = x227.in(x150);

		return Formula.compose(FormulaOperator.AND, x170, x186, x195, x198, x206, x208, x217, x219, x226, x78, x80,
				x83, x85, x88, x91, x94, x96, x99, x102, x105, x108, x111, x113, x116, x119, x121, x124, x126, x129,
				x132, x135, x137, x140, x143, x146, x152, x154, x157, x162, x164);
	}

	private static Formula f13() {
		Expression x169 = orcid.intersection(ptcris);
		Formula x168 = x169.no();

		Expression x139 = x35.union(x36);
		Expression x142 = x139.union(x37);
		Expression x145 = x142.union(x38);

		Expression x151 = x145.union(x39);
		Expression x150 = x151.union(x40);

		Variable x230 = Variable.unary("hippocratic_import_this");
		Decls x229 = x230.oneOf(x150);
		Variable x233 = Variable.unary("hippocratic_import_r");
		Decls x232 = x233.oneOf(orcid);
		Expression x236 = x230.join(uids);
		Expression x235 = x236.join(x233);
		Expression x239 = x230.join(x58);
		Expression x238 = x239.join(uids);
		Expression x237 = x238.join(x233);
		Formula x234 = x235.eq(x237);
		Formula x231 = x234.forAll(x232);
		Formula x228 = x231.forAll(x229);

		return x168.and(x228);
	}
}
