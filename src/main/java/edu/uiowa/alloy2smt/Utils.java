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
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import edu.uiowa.alloy2smt.translators.Translation;

public class Utils
{
    public static String translateFromFile(String filePath, String assertion)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SmtTranslator     translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram              program     = translator.translate(assertion);
        SmtLibPrettyPrinter     printer     = new SmtLibPrettyPrinter();

        printer.visit(program);

        String                  output      = printer.getSmtLib();
        return output;
    }

    public static String translateFromString(String alloyProgram, String assertion)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SmtTranslator     translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram              program     = translator.translate(assertion);
        SmtLibPrettyPrinter     printer     = new SmtLibPrettyPrinter();

        printer.visit(program);

        String                  output      = printer.getSmtLib();
        return output;
    }

    public static Translation translate(String alloyProgram)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SmtTranslator     translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram              program     = translator.translate(null);
        Mapper                  mapper      = translator.generateMapper();
        SmtLibPrettyPrinter     printer     = new SmtLibPrettyPrinter();

        printer.visit(program);

        String                  output      = printer.getSmtLib();

        Translation             translation = new Translation(translator, program, mapper, output);

        return translation;
    }

    public static SmtProgram getSmtAstFromFile(String filePath, String assertion)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromFile(null, null, filePath);
        Alloy2SmtTranslator     translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram              program     = translator.translate(assertion);
        return program;
    }

    public static SmtProgram getSmtAstFromString(String alloyProgram, String assertion)
    {
        CompModule              alloyModel  = CompUtil.parseEverything_fromString(null, alloyProgram);
        Alloy2SmtTranslator     translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram              program     = translator.translate(assertion);
        return program;
    }
}
