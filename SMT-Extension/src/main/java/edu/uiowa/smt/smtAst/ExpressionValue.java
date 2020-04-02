package edu.uiowa.smt.smtAst;

public class ExpressionValue extends SmtAst
{
    private final Expression expression;
    private final Expression value;

    public ExpressionValue(Expression expression, Expression value)
    {
        this.expression = expression;
        this.value = value;
    }

    public Expression getExpression()
    {
        return expression;
    }

    public Expression getValue()
    {
        return value;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }
}
