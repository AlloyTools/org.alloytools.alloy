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
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtProgram;

import java.util.Map;

public class Utils
{
    public static Translation translateFromFile(String filePath, AlloySettings settings)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, null, filePath);
        return getTranslation(alloyModel, settings);
    }

    public static Translation translate(String alloyProgram, AlloySettings settings)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromString(null, alloyProgram);
        return getTranslation(alloyModel, settings);
    }

    public static Translation translate(Map<String, String> alloyFiles, String originalFileName, int resolutionMode,
                                        AlloySettings settings)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, alloyFiles, originalFileName, resolutionMode);
        return getTranslation(alloyModel, settings);
    }

    private static Translation getTranslation(CompModule alloyModel, AlloySettings settings)
    {
        Alloy2SmtTranslator translator  = new Alloy2SmtTranslator(alloyModel);
        SmtProgram program              = translator.translate();
        Mapper mapper                   = translator.generateMapper();
        SmtLibPrettyPrinter printer     = new SmtLibPrettyPrinter(settings);
        printer.visit(program);

        String smtScript                = printer.getSmtLib();

        Translation translation         = new Translation(translator, program, mapper, smtScript, settings);
        return translation;
    }
}
