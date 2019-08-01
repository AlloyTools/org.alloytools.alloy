/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 *
 * @author Mudathir Mohamed, Paul Meng
 */
public class ITEExpression extends Expression
{
    private final Expression                  condExpr;
    private final Expression                  thenExpr;
    private final Expression                  elseExpr;
    
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
        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        if(condExpr.getSort() != AbstractTranslator.boolSort)
        {
            throw new RuntimeException(String.format("The sort '%1$s' of the condition expression is not boolean", condExpr.getSort()));
        }

        if(!thenExpr.getSort().equals(elseExpr.getSort()))
        {
            throw new RuntimeException(String.format("The sort '%1$s' of then expression is different than the sort '%1$s' of else expression", thenExpr.getSort(), elseExpr.getSort()));
        }
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

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return this.thenExpr.getSort();
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        Expression evaluatedCondition =  condExpr.evaluate(functions);
        if(!(evaluatedCondition instanceof BoolConstant))
        {
            throw new RuntimeException("Expected a boolean constant but got " + evaluatedCondition);
        }
        boolean isTrue = Boolean.parseBoolean(((BoolConstant) evaluatedCondition).getValue());
        if(isTrue)
        {
            return thenExpr.evaluate(functions);
        }
        else
        {
            return elseExpr.evaluate(functions);
        }
    }
    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof ITEExpression))
        {
            return false;
        }
        ITEExpression iteObject = (ITEExpression) object;
        return  condExpr.equals(iteObject.condExpr) &&
                thenExpr.equals(iteObject.thenExpr) &&
                elseExpr.equals(iteObject.elseExpr);
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        if (condExpr.equals(newVariable) || thenExpr.equals(newVariable) || elseExpr.equals(newVariable))
        {
            throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
        }
        Expression newCondition = condExpr.substitute(oldVariable, newVariable);
        Expression newThen = elseExpr.substitute(oldVariable, newVariable);
        Expression newElse = elseExpr.substitute(oldVariable, newVariable);
        return new ITEExpression(newCondition, newThen, newElse);
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        if(oldExpression.equals(this))
        {
            return newExpression;
        }
        Expression newCondition = condExpr.replace(oldExpression, newExpression);
        Expression newThen = elseExpr.replace(oldExpression, newExpression);
        Expression newElse = elseExpr.replace(oldExpression, newExpression);
        return new ITEExpression(newCondition, newThen, newElse);
    }
}
