package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class CommandTranslationTests
{

    @Test
    void noCommand()
    {
        String alloy = "sig A {}\n";

        Translation translation = Utils.translate(alloy);
        String command = translation.translateCommand(0, false);

        Assertions.assertEquals(1, translation.getCommands().size());
    }

    @Test
    void runCommand1()
    {
        String alloy =
                "sig A {}\n" +
                "run command1 {#A = 1 or #A = 2} for 10";

        Translation translation = Utils.translate(alloy);

        Assertions.assertFalse(translation.getSmtScript().contains("(check-sat)"));
        Assertions.assertFalse(translation.getSmtScript().contains("(get-model)"));

        String command = translation.translateCommand(0, false);

        Assertions.assertEquals(
                "; command1\n" +
                "(assert (or (exists ((_a3 Atom)) (and (= this_A (singleton (mkTuple _a3))) true)) (exists ((_a4 Atom)(_a5 Atom)) (and (= this_A (insert (mkTuple _a5) (singleton (mkTuple _a4)))) (distinct _a4 _a5)))))\n",
                command);
    }


    @Test
    void runCommand2()
    {
        String alloy =
                "sig A {}\n" +
                "run command1 {#A = 1 or #A = 2} for 10\n" +
                // multiple commands can share the same label
                "run command1 {no A} for 10\n"
                ;
        Translation translation = Utils.translate(alloy);

        String command = translation.translateCommand(1, true);

        Assertions.assertEquals(
                "; command1\n" +
                "(assert (= this_A (as emptyset (Set (Tuple Atom)))))\n",
                command);
    }


    @Test
    void runCommandWithNewFunctionDeclaration()
    {
        String alloy =
                "sig A0, A1, A2 in Int{}\n" +
                "run command1 {A0 > A1 + A2}";

        Translation translation = Utils.translate(alloy);
        String command = translation.translateCommand(0, false);

        Assertions.assertEquals(
                "(declare-fun _GT ((Set (Tuple Int))(Set (Tuple Int))) Bool)\n" +
                        "; command1\n" +
                        "(assert (_GT this_A0 (union this_A1 this_A2)))\n",
                command);
    }


    @Test
    void checkCommand1()
    {
        String alloy =
                "sig A {}\n" +
                "assert command1{some A}\n" +
                "check command1 for 10\n" +
                "assert command2 {some A or no A} \n" +
                "check command2 for 10\n";

        Translation translation = Utils.translate(alloy);

        String command1 = translation.translateCommand(0, true);

        Assertions.assertEquals(
                "; command1\n" +
                        "(assert (not " +
                                    "(exists ((_x1 Atom)) " +
                                        "(member (mkTuple _x1) this_A))))\n",
                command1);

        String command2 = translation.translateCommand(1, true);

        Assertions.assertEquals(
                "; command2\n" +
                        "(assert (not " +
                                    "(or " +
                                        "(exists ((_x2 Atom)) " +
                                            "(member (mkTuple _x2) this_A)) " +
                                        "(= this_A " +
                                            "(as emptyset (Set (Tuple Atom)))))))\n",
                command2);
    }
}