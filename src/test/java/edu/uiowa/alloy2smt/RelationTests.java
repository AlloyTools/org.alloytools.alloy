package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;


class RelationTests extends TestBase
{

    @Test
    public void unaryFieldRelation()
    {

        String input =
                "sig Addr {}\n" +
                "sig Book {\n" +
                    "addr: Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix  +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product this_Book this_Addr)))\n" +
                "(assert (forall ((_x1 Atom)) (=> (member (mkTuple _x1 ) this_Book) " +
                "(exists ((_x2 Atom)) " +
                "(and (member (mkTuple _x2 ) this_Addr) " +
                "(and (member (mkTuple _x1 _x2 ) this_Book_addr) " +
                "(forall ((_x3 Atom)) (=> (and " +
                "(member (mkTuple _x3 ) this_Addr) " +
                "(not (= _x3 _x2))) " +
                "(not (member (mkTuple _x1 _x3 ) this_Book_addr))))))))))\n";

        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void unaryFieldRelationOne()
    {

        String input =
                "sig Addr {}\n" +
                "sig Book {\n" +
                "addr: one Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product this_Book this_Addr)))\n" +
                "(assert (forall ((_x1 Atom)) (=> (member (mkTuple _x1 ) this_Book) " +
                                                "(exists ((_x2 Atom)) " +
                                                    "(and (member (mkTuple _x2 ) this_Addr) " +
                                                        "(and (member (mkTuple _x1 _x2 ) this_Book_addr) " +
                                                            "(forall ((_x3 Atom)) (=> (and " +
                                                                "(member (mkTuple _x3 ) this_Addr) " +
                                                                "(not (= _x3 _x2))) " +
                                                            "(not (member (mkTuple _x1 _x3 ) this_Book_addr))))))))))\n";

        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void unaryFieldRelationSome()
    {

        String input =
                "sig Addr {}\n" +
                "sig Book {\n" +
                "addr: some Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product this_Book this_Addr)))\n" +
                "(assert (forall ((_x1 Atom)) (=> (member (mkTuple _x1 ) this_Book) " +
                                                "(exists ((_x2 Atom)) " +
                                                    "(and (member (mkTuple _x2 ) this_Addr) " +
                                                        "(member (mkTuple _x1 _x2 ) this_Book_addr))))))\n";

        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void unaryFieldRelationSet()
    {

        String input =
                "sig Addr {}\n" +
                "sig Book {\n" +
                "addr: set Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product this_Book this_Addr)))\n";
        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void unaryFieldRelationLone()
    {

        String input =
                "sig Addr {}\n" +
                "sig Book {\n" +
                "addr: lone Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product this_Book this_Addr)))\n" +
                "(assert (forall ((_x1 Atom)) (=> (member (mkTuple _x1 ) this_Book) (or (forall ((_x2 Atom)) (=> (member (mkTuple _x2 ) this_Addr) (not (member (mkTuple _x1 _x2 ) this_Book_addr)))) (exists ((_x3 Atom)) (and (member (mkTuple _x3 ) this_Addr) (and (member (mkTuple _x1 _x3 ) this_Book_addr) (forall ((_x4 Atom)) (=> (and (member (mkTuple _x4 ) this_Addr) (not (= _x4 _x3))) (not (member (mkTuple _x1 _x4 ) this_Book_addr)))))))))))\n";

        assertEquals(expected + getSuffix(), actual);
    }

    @Disabled
    @Test
    public void unaryFieldRelationSetSet()
    {

        String input =
                "sig Name, Addr {}\n" +
                "sig Book {\n" +
                "addr: Name -> Addr}"; // set -> set

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Name () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product (product this_Book this_Name) this_Addr)))\n";
        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void multiArityFieldRelationSet_SomeSetSet()
    {

        String input =
                "sig A, B, C {}\n" +
                "sig D {\n" +
                "r: A set -> some B set -> set C}\n" +
                "fact f{#r >= 1}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(declare-fun this_D () (Set (Tuple Atom )))\n" +
                "(declare-fun this_D_r () (Set (Tuple Atom Atom Atom Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom Atom Atom ))\n" +
                "(assert (subset this_D_r (product (product (product this_D this_A) this_B) this_C)))\n" +
                "(assert (forall ((_x1 (Tuple Atom ))) " +
                    "(=> (member _x1 this_D) " +
                        "(forall ((_x2 (Tuple Atom ))) " +
                            "(=> (member _x2 this_A) " +
                                "(exists ((_x3 (Tuple Atom Atom ))) " +
                                    "(member _x3 (join (singleton _x2) (join (singleton _x1) this_D_r)))))))))\n" +
                "(assert (= _S1 (singleton _a1)))\n" +
                "; f\n" +
                "(assert (subset _S1 this_D_r))\n";
        assertEquals(expected + getSuffix(), actual);
    }

    @Test
    public void multiArityFieldRelationSetSetSet_Some()
    {

        String input =
                "sig A, B, C {}\n" +
                "sig D {\n" +
                "r: (A set -> set B) set -> some C}\n" +
                "fact f{#r >= 1}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_A () (Set (Tuple Atom )))\n" +
                "(declare-fun this_B () (Set (Tuple Atom )))\n" +
                "(declare-fun this_C () (Set (Tuple Atom )))\n" +
                "(declare-fun this_D () (Set (Tuple Atom )))\n" +
                "(declare-fun this_D_r () (Set (Tuple Atom Atom Atom Atom )))\n" +
                "(declare-fun _S1 () (Set (Tuple Atom Atom Atom Atom )))\n" +
                "(declare-const _a1 (Tuple Atom Atom Atom Atom ))\n" +
                "(assert (subset this_D_r (product (product (product this_D this_A) this_B) this_C)))\n" +
                "(assert (forall ((_x1 (Tuple Atom ))) " +
                    "(=> (member _x1 this_D) " +
                        "(forall ((_x2 (Tuple Atom ))(_x3 (Tuple Atom ))) " +
                            "(=> (and (member _x2 this_A) (member _x3 this_B)) " +
                                "(exists ((_x4 (Tuple Atom ))) " +
                                    "(member _x4 " +
                                        "(join (singleton _x3) (join (singleton _x2) (join (singleton _x1) this_D_r))))))))))\n" +
                "(assert (= _S1 (singleton _a1)))\n" +
                "; f\n" +
                "(assert (subset _S1 this_D_r))\n";
        assertEquals(expected + getSuffix(), actual);
    }

    @Disabled
    @Test
    public void multiArityFieldRelationSetOne()
    {

        String input =
                "sig Name, Addr {}\n" +
                "sig Book {\n" +
                "addr: Name set -> one Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_Name () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product (product this_Book this_Name) this_Addr)))\n";
        assertEquals(expected + getSuffix(), actual);
    }

    @Disabled
    @Test
    public void translateAddressBookExample()
    {

        String input = "module tour/addressBook1h ------- Page 14..16\n" +
                "\n" +
                "sig Name, Addr { }\n" +
                "\n" +
                "sig Book {\n" +
                "\taddr: Name -> lone Addr\n" +
                "}\n" +
                "\n" +
                "pred show [b: Book] {\n" +
                "\t#b.addr > 1\n" +
                "\t#Name.(b.addr) > 1\n" +
                "}\n" +
                "run show for 3 but 1 Book\n" +
                "\n" +
                "pred add [b, b': Book, n: Name, a: Addr] {\n" +
                "\tb'.addr = b.addr + n->a\n" +
                "}\n" +
                "\n" +
                "pred del [b, b': Book, n: Name] {\n" +
                "\tb'.addr = b.addr - n->Addr\n" +
                "}\n" +
                "\n" +
                "fun lookup [b: Book, n: Name] : set Addr {\n" +
                "\tn.(b.addr)\n" +
                "}\n" +
                "\n" +
                "pred showAdd [b, b': Book, n: Name, a: Addr] {\n" +
                "\tadd [b, b', n, a]\n" +
                "\t#Name.(b'.addr) > 1\n" +
                "}\n" +
                "run showAdd for 3 but 2 Book\n" +
                "\n" +
                "assert delUndoesAdd {\n" +
                "\tall b, b', b'': Book, n: Name, a: Addr |\n" +
                "\t\tno n.(b.addr) and add [b, b', n, a] and del [b', b'', n]\n" +
                "\t\timplies\n" +
                "\t\tb.addr = b''.addr\n" +
                "}\n" +
                "\n" +
                "assert addIdempotent {\n" +
                "\tall b, b', b'': Book, n: Name, a: Addr |\n" +
                "\t\tadd [b, b', n, a] and add [b', b'', n, a]\n" +
                "\t\timplies\n" +
                "\t\tb'.addr = b''.addr\n" +
                "}\n" +
                "\n" +
                "assert addLocal {\n" +
                "\tall b, b': Book, n, n': Name, a: Addr |\n" +
                "\t\tadd [b, b', n, a] and n != n\n" +
                "\t\timplies\n" +
                "\t\tlookup [b, n'] = lookup [b', n']\n" +
                "}\n" +
                "\n" +
                "// This command should not find any counterexample.\n" +
                "check delUndoesAdd for 3\n" +
                "\n" +
                "// This command should not find any counterexample.\n" +
                "check delUndoesAdd for 10 but 3 Book\n" +
                "\n" +
                "// This command should not find any counterexample.\n" +
                "check addIdempotent for 3\n" +
                "\n" +
                "// This command should not find any counterexample.\n" +
                "check addLocal for 3 but 2 Book\n" +
                "fun addrIdentity [a : addr] : addr {\n" +
                "\ta\n" +
                "}";

        String actual = Utils.translateFromString(input);
        String expected = "?";
        assertEquals(expected + getSuffix(), actual);
    }
}