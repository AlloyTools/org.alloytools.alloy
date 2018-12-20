package edu.uiowa.alloy2smt.smtparser;

import edu.uiowa.alloy2smt.smtparser.antlr.SmtBaseVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;

import java.util.HashMap;
import java.util.Map;

public class SmtVisitor extends SmtBaseVisitor<Map<String, String>>
{
    private Map<String, String> model = new HashMap<>();

    @Override
    public Map<String, String> visitModel(SmtParser.ModelContext ctx)
    {
        for (SmtParser.DefinitionsContext context: ctx.definitions())
        {
            this.visitDefinitions(context);
        }
        return model;
    }

    @Override
    public Map<String, String> visitDefinitions(SmtParser.DefinitionsContext ctx)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
}