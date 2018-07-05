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
import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.translators.Alloy2SMTTranslator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Utils
{

    public static String translateFromFile(String filePath)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SMTTranslator translator  = new Alloy2SMTTranslator(alloyModel);
        SMTProgram              program     = translator.execute();
        SMTLibPrettyPrinter     printer     = new SMTLibPrettyPrinter(program);
        String                  output      = printer.print();
        return output;
    }

    public static String translateFromString(String alloyProgram)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTProgram              program     = translator.execute();
        SMTLibPrettyPrinter     printer     = new SMTLibPrettyPrinter(program);
        String                  output      = printer.print();
        return output;
    }

    public static SMTProgram getSMTAstFromFile(String filePath)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTProgram              program     = translator.execute();
        return program;
    }

    public static SMTProgram getSMTAstFromString(String alloyProgram)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SMTTranslator     translator  = new Alloy2SMTTranslator(alloyModel);
        SMTProgram              program     = translator.execute();
        return program;
    }
}
