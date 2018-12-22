package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class AtomConstant extends Expression
{

    private String name;

    public AtomConstant(String name)
    {
        this.name = name;
    }

    public String getName()
    {
        return name;
    }

    @Override
    public void accept(SMTAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
