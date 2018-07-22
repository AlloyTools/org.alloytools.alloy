package edu.uiowa.alloy2smt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ExampleTests extends TestBase
{
    @Test
    public void fileSystem1()
    {
        String input =
        "abstract sig FileSystemObj{}\n" +
        "sig File extends FileSystemObj{}\n" +
        "sig Dir extends FileSystemObj{\n" +
        "    contents: set FileSystemObj\n" +
        "}\n" +
        "fact fileFact{\n" +
        "all f: File | some d: Dir |\n" +
        "\t         f in d.contents\n" +
        "}";

        String actual = Utils.translateFromString(input);
        String expected =
                prefix +
                "(declare-fun this_FileSystemObj () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_File () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_Dir () (Set (Tuple Atom )))\n" +
                        "(declare-fun this_Dir_contents () (Set (Tuple Atom Atom )))\n" +
                        "(assert (subset this_File this_FileSystemObj))\n" +
                        "(assert (subset this_Dir this_FileSystemObj))\n" +
                        "(assert (subset this_Dir_contents (product this_Dir this_FileSystemObj)))\n" +
                        "(assert (= (intersection this_File this_Dir) (as emptyset (Set (Tuple Atom )))))\n" +
                        "(assert (= this_FileSystemObj (union this_File this_Dir)))\n" +
                        "; fileFact\n" +
                        "(assert (forall ((f Atom)) " +
                            "(=> (member (mkTuple f ) this_File) " +
                                "(exists ((d Atom)) " +
                                    "(and (member (mkTuple d ) this_Dir) " +
                                        "(subset (singleton (mkTuple f )) " +
                                                "(join (singleton (mkTuple d )) this_Dir_contents)))))))\n" ;
        assertEquals(expected + getSuffix(), actual);
    }
}
