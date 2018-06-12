package edu.uiowa.alloy2smt;

import edu.uiowa.alloy2smt.smtAst.SMTAst;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


class Alloy2SMTTranslatorTest
{
    @Test
    public void executeTest()
    {
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator();
        SMTAst                  root        = translator.execute();
        assertNotNull(root);
    }
}