package edu.uiowa.alloy2smt.smtparser;

import edu.uiowa.alloy2smt.smtAst.Declaration;
import edu.uiowa.alloy2smt.smtAst.SMTAst;
import edu.uiowa.alloy2smt.smtAst.SMTProgram;
import edu.uiowa.alloy2smt.smtAst.Sort;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtBaseVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;

public class SmtModelVisitor extends SmtBaseVisitor<SMTAst>
{
    private SMTProgram model = new SMTProgram();

    public SMTProgram getModel()
    {
        return  model;
    }

    @Override
    public SMTAst visitSortDeclaration(SmtParser.SortDeclarationContext ctx)
    {
        String  sortName    = ctx.sortName().getText();
        int     arity       = Integer.parseInt(ctx.arity().getText());
        Sort    sort        = new Sort(sortName, arity);

        model.addSort(sort);
        return sort;
    }

    @Override
    public SMTAst visitSortName(SmtParser.SortNameContext ctx)
    {
        String  sortName    = ctx.getText();
        Sort    sort        = model.getSorts().stream()
                .filter(s -> sortName.equals(s.getName()))
                .findFirst()
                .orElse(null);
        if(sort == null)
        {
            sort = new Sort(sortName, 0);
            this.model.addSort(sort);
        }
        return sort;
    }

    @Override
    public SMTAst  visitDefinition(SmtParser.DefinitionContext ctx)
    {
        throw new UnsupportedOperationException("Not implemented yet");
    }
}