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
    // rewrite the current node without rewriting its children
    RewriteAgain,
    // rewrite the current node along with its children
    RewriteAgainFull;

    public SmtRewriteResult make(SmtAst smtAst)
    {
      return new SmtRewriteResult(this, smtAst);
    }
  }
}
