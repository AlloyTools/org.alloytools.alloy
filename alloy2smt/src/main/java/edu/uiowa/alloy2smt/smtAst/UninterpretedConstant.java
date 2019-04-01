package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;

public class UninterpretedConstant extends Expression
{

    private String name;
    private UninterpretedSort sort;

    public UninterpretedConstant(String name, UninterpretedSort sort)
    {
        this.name = name;
        this.sort = sort;
    }

    public String getName()
    {
        return name;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return sort;
    }
}
