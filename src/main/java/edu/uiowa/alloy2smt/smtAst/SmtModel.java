package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

import java.util.ArrayList;
import java.util.List;

public class SmtModel extends SmtAst
{
    protected final List<FunctionDefinition>     functionDefinitions  = new ArrayList<>();
    protected final List<Sort>                   sorts                = new ArrayList<>();

    public void addSort(Sort sort)
    {
        if(sort != null)
        {
            this.sorts.add(sort);
        }
    }

    public void addFunctionDefinition(FunctionDefinition functionDefinition)
    {
        if(functionDefinition != null)
        {
            this.functionDefinitions.add(functionDefinition);
        }
    }

    public List<Sort> getSorts()
    {
        return this.sorts;
    }

    public List<FunctionDefinition> getFunctionDefinitions() {
        return this.functionDefinitions;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        throw new UnsupportedOperationException();
    }
}
