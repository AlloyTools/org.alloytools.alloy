/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import java.util.HashMap;
import java.util.Map;

/**
 *
 * @author Paul Meng
 */
public class LetExpression extends Expression
{
    private final Expression                  expr;
    private final Map<String, Expression>     letVars;
    private final Op                          op;
    
    public LetExpression(Op op, Map<String, Expression> letVars, Expression expr)
    {
        this.letVars    = new HashMap<>();
        this.expr       = expr;
        this.op         = op;
        for(Map.Entry<String, Expression> var : letVars.entrySet())
        {
            this.letVars.put(var.getKey(), var.getValue());
        }
    }

    
    public Map<String, Expression> getLetVars()
    {
        return this.letVars;
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
}
