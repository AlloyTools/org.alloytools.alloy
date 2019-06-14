/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author Paul Meng
 */
public class LetExpression extends Expression
{
    private final Expression                  expr;
    private final Map<String, Expression> letVariables;
    private final Op                          op;
    
    public LetExpression(Op op, Map<String, Expression> letVars, Expression expr)
    {
        this.letVariables = new HashMap<>();
        this.expr       = expr;
        this.op         = op;
        for(Map.Entry<String, Expression> var : letVars.entrySet())
        {
            this.letVariables.put(var.getKey(), var.getValue());
        }
    }

    
    public Map<String, Expression> getLetVariables()
    {
        return this.letVariables;
    }
    
    public Expression getExpression()
    {
        return this.expr;
    }

    public Op getOp()
    {
        return this.op;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }

    public enum Op 
    {        
        LET ("let");    

        private final String opStr;

        private Op(String op) 
        {
            this.opStr = op;
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }        
    }

    @Override
    public Sort getSort()
    {
        return expr.getSort();
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        throw new UnsupportedOperationException();
    }
}
