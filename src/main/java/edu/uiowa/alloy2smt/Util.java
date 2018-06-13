/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.uiowa.alloy2smt.printers.SMTLibPrettyPrinter;
import edu.uiowa.alloy2smt.smtAst.SMTAst;

public class Util
{

    public static String translateFromFile(String filePath)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTAst                  root        = translator.execute();
        SMTLibPrettyPrinter     printer     = new SMTLibPrettyPrinter(root);
        String                  output      = printer.print();
        return output;
    }

    public static String translateFromString(String alloyProgram)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTAst                  root        = translator.execute();
        SMTLibPrettyPrinter     printer     = new SMTLibPrettyPrinter(root);
        String                  output      = printer.print();
        return output;
    }

    public static SMTAst getSMTAstFromFile(String filePath)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTAst                  root        = translator.execute();
        return root;
    }

    public static SMTAst getSMTAstFromString(String alloyProgram)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTAst                  root        = translator.execute();
        return root;
    }
}
