package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.List;

public class SmtValues extends SmtAst
{
    private final List<ExpressionValue> values;

    public SmtValues(List<ExpressionValue> values)
    {
        this.values = values;
    }

    public List<ExpressionValue> getValues()
    {
        return values;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    public Expression getExpression(int index)
    {
        return values.get(index).getExpression();
    }

    public Expression getValue(int index)
    {
        return values.get(index).getValue();
    }
}
