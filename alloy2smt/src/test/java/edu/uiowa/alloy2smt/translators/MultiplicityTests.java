package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.Utils;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class MultiplicityTests
{
    @Test
    public void oneSetDeclaration()
    {
        String alloy =  "sig A {} fact f {some x: one A | some A}";

        Translation translation = Utils.translate(alloy);

        String script = translation.getSmtScript();

        Assertions.assertTrue(script.contains("; f\n" +
                "(assert (exists ((x Atom)) (and (and true (member (mkTuple x) this_A)) (exists ((_x1 Atom)) (member (mkTuple _x1) this_A)))))\n"));
    }

    @Test
    public void loneSetDeclaration()
    {
        String alloy =  "sig A {} fact f {some x: lone A | lone x and no x}";

        Translation translation = Utils.translate(alloy);

        String script = translation.getSmtScript();

        Assertions.assertTrue(script.contains("; f\n" +
                "(assert (exists ((x Atom)) (and (and true (member (mkTuple x) this_A)) (exists ((_x1 Atom)) (member (mkTuple _x1) this_A)))))\n"));
    }
}
