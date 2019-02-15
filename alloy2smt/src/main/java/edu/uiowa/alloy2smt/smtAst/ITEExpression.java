/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

/**
 *
 * @author Mudathir Mohamed, Paul Meng
 */
public class ITEExpression extends Expression
{
    private final Expression                  condExpr;
    private final Expression                  thenExpr;
    private final Expression                  elseExpr;
    private final Op                          op = Op.ITE;
    
    public ITEExpression(Expression condExpr, Expression thenExpr, Expression elseExpr)
    {
        if(condExpr == null)
        {
            throw new RuntimeException("Condition expression of the ite is null");
        }
        if(thenExpr == null)
        {
            throw new RuntimeException("Then expression of the ite is null");
        }
        if(elseExpr == null)
        {
            throw new RuntimeException("Else expression of the ite is null");
        }
        this.condExpr = condExpr;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }

    
    public Expression getCondExpression()
    {
        return this.condExpr;
    }
    
    public Expression getThenExpression()
    {
        return this.thenExpr;
    }    
    
    public Expression getElseExpression()
    {
        return this.elseExpr;
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
        ITE ("ite");    

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
        return this.thenExpr.getSort();
    }
}
