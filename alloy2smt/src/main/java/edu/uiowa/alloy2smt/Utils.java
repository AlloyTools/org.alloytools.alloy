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
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtProgram;

import java.util.Map;

public class Utils
{
    public static Translation translateFromFile(String filePath, Map<String, String> options)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, null, filePath);
        return getTranslation(alloyModel, options);
    }

    public static Translation translate(String alloyProgram, Map<String, String> options)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromString(null, alloyProgram);
        return getTranslation(alloyModel, options);
    }

    public static Translation translate(Map<String, String> alloyFiles, String originalFileName, int resolutionMode, Map<String, String> options)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, alloyFiles, originalFileName, resolutionMode);
        return getTranslation(alloyModel, options);
    }

    private static Translation getTranslation(CompModule alloyModel, Map<String, String> options)
    {
        Alloy2SmtTranslator translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram program              = translator.translate();
        Mapper mapper                   = translator.generateMapper();
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter(options);
        printer.visit(program);

        String smtScript                = printer.getSmtLib();

        Translation translation         = new Translation(translator, program, mapper, smtScript);
        return translation;
    }
}
