package edu.uiowa.shared;

import edu.mit.csail.sdg.ast.Command;
import edu.uiowa.alloy2smt.smtAst.SmtModel;

public class CommandResult
{
    public int index;
    public Command command;
    public String result;
    public SmtModel smtModel;
}
