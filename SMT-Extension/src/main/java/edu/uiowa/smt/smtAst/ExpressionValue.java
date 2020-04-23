package edu.uiowa.smt.smtAst;

public class ExpressionValue extends SmtAst
{
  private final SmtExpr smtExpr;
  private final SmtExpr value;

  public ExpressionValue(SmtExpr smtExpr, SmtExpr value)
  {
    this.smtExpr = smtExpr;
    this.value = value;
  }

  public SmtExpr getSmtExpr()
  {
    return smtExpr;
  }

  public SmtExpr getValue()
  {
    return value;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }
}
