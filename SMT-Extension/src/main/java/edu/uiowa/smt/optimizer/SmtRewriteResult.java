package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.smtAst.SmtAst;

public class SmtRewriteResult
{
  public Status status;
  public SmtAst smtAst;

  private SmtRewriteResult(Status status, SmtAst smtAst)
  {
    this.status = status;
    this.smtAst = smtAst;
  }

  public enum Status
  {
    // rewriting is finished
    Done,
    // rewrite again
    RewriteAgain;

    public SmtRewriteResult make(SmtAst smtAst)
    {
      return new SmtRewriteResult(this, smtAst);
    }
  }
}
