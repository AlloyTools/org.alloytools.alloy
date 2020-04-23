package edu.uiowa.smt.smtAst;

import java.util.List;

public class SmtUnsatCore extends SmtAst
{
  private final List<String> core;

  public SmtUnsatCore(List<String> core)
  {
    this.core = core;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  public List<String> getCore()
  {
    return core;
  }
}
