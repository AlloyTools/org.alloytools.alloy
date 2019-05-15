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
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.*;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import edu.uiowa.alloy2smt.translators.Translation;

import java.util.Map;

public class Utils
{
    public static Translation translateFromFile(String filePath)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, null, filePath);
        return getTranslation(alloyModel);
    }

    private static String translateFromModel(CompModule alloyModel, int commandIndex, boolean includeScope)
    {
        Alloy2SmtTranslator translator      = new Alloy2SmtTranslator(alloyModel);
        SmtProgram          smtProgram      = translator.translate();
        SmtLibPrettyPrinter programPrinter  = new SmtLibPrettyPrinter();

        programPrinter.visit(smtProgram);

        String              program         = programPrinter.getSmtLib();
        Assertion           assertion       = translator.translateCommand(commandIndex, includeScope);
        SmtLibPrettyPrinter commandPrinter  = new SmtLibPrettyPrinter();

        commandPrinter.visit(assertion);

        String              command         = commandPrinter.getSmtLib();

        return program + command + SmtLibPrettyPrinter.CHECK_SAT + "\n" + SmtLibPrettyPrinter.GET_MODEL + "\n";
    }

    public static String translateFromString(String alloyProgram, int commandIndex, boolean includeScope)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromString(null, alloyProgram);
        return translateFromModel(alloyModel, commandIndex, includeScope);
    }

    public static Translation translate(String alloyProgram)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromString(null, alloyProgram);
        return getTranslation(alloyModel);
    }

    public static Translation translate(Map<String, String> alloyFiles, String originalFileName, int resolutionMode)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, alloyFiles, originalFileName, resolutionMode);
        return getTranslation(alloyModel);
    }

    private static Translation getTranslation(CompModule alloyModel)
    {
        Alloy2SmtTranslator translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram program              = translator.translate();
        Mapper mapper                   = translator.generateMapper();
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter();
        printer.visit(program);

        String smtScript                = printer.getSmtLib();
        Translation translation         = new Translation(translator, program, mapper, smtScript);
        return translation;
    }
}
