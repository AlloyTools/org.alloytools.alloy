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
import edu.uiowa.smt.optimizer.SmtOptimizer;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;
import edu.uiowa.smt.smtAst.SmtScript;

import java.util.Map;

public class Utils
{
    public static Translation translateFromFile(String filePath, AlloySettings settings)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromFile(null, null, filePath);
        return getTranslation(alloyModel, settings);
    }

    public static Translation translate(String alloyScript, AlloySettings settings)
    {
        CompModule alloyModel = CompUtil.parseEverything_fromString(null, alloyScript);
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
        Alloy2SmtTranslator translator = new Alloy2SmtTranslator(alloyModel, settings);
        SmtScript script = translator.translate();
        script = SmtOptimizer.optimize(script);
        Mapper mapper = translator.generateMapper();
        SmtLibPrettyPrinter printer = new SmtLibPrettyPrinter(settings);
        printer.visit(script);

        String smtScript = printer.getSmtLib();

        Translation translation = new Translation(translator, script, mapper, smtScript, settings);
        return translation;
    }
}
