package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.smtAst.SMTAst;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


class Alloy2SMTTranslatorTest
{
    @Test
    public void executeSimpleModel()
    {

        String input =
                "sig Name, Addr {}\n" +
                "sig Book {\n" +
                "addr: Name -> Addr}";

        String actual = Utils.translateFromString(input);
        String expected =
                "(set-logic ALL)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :finite-model-find true)\n" +
                "(declare-sort Atom 0)\n" +
                "(declare-fun this_Name () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Addr () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book () (Set (Tuple Atom )))\n" +
                "(declare-fun this_Book_addr () (Set (Tuple Atom Atom Atom )))\n" +
                "(assert (subset this_Book_addr (product (product this_Book this_Name) this_Addr)))\n";
        assertEquals(expected, actual);
    }

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
        assertEquals(expected, actual);
    }
}