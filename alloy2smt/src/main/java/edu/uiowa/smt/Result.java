package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.SmtModel;

public class Result
{
    public final String smtProgram;
    public final String satResult;
    public SmtModel smtModel;

    public Result(String smtProgram, String satResult)
    {
        this.smtProgram = smtProgram;
        this.satResult = satResult;
    }
}
