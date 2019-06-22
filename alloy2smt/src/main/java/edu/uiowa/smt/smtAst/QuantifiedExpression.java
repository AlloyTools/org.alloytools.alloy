/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class QuantifiedExpression extends Expression
{
    private final Expression expr;
    private final List<VariableDeclaration> variables;
    private final Op op;
    
    private QuantifiedExpression(Op op, List<VariableDeclaration> variables, Expression expr)
    {
        this.variables = new ArrayList<>();
        this.expr       = expr;
        this.op         = op;
        for(VariableDeclaration bdVar : variables)
        {
            this.variables.add(bdVar);
        }
        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        if(expr.getSort() != AbstractTranslator.boolSort)
        {
            throw new RuntimeException(String.format("The sort '%1$s' of the quantified expression is not boolean", expr.getSort()));
        }
    }

    private QuantifiedExpression(Op op, Expression expr, VariableDeclaration... variables)
    {
        this.variables = Arrays.asList(variables);
        this.expr       = expr;
        this.op         = op;
    }
    
    public List<VariableDeclaration> getVariables()
    {
        return this.variables;
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
        FORALL ("forall"),
        EXISTS ("exists");

        private final String opStr;

        Op(String op)
        {
            this.opStr = op;
        }

        public QuantifiedExpression make(Expression expr, VariableDeclaration... variables)
        {
            return new QuantifiedExpression(this, expr, variables);
        }

        public QuantifiedExpression make(Expression expr, List<VariableDeclaration> variables)
        {
            return new QuantifiedExpression(this, variables, expr);
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
        return AbstractTranslator.boolSort;
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof QuantifiedExpression))
        {
            return false;
        }
        QuantifiedExpression quantifiedObject = (QuantifiedExpression) object;
        if(! variables.equals(quantifiedObject.variables))
        {
            return false;
        }
        return op ==  quantifiedObject.op &&
                expr.equals(quantifiedObject.expr);
    }

    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        Expression body = expr;
        List<VariableDeclaration> variables = new ArrayList<>(this.variables);
        // check if the new variable is declared
        for (Declaration declaration: this.variables)
        {
            if(declaration.getVariable().equals(newVariable))
            {
                // choose a new name for the declared variable
                VariableDeclaration newDeclaration = new VariableDeclaration(TranslatorUtils.getNewSetName(), declaration.getSort(), null);
                if(declaration instanceof  VariableDeclaration)
                {
                    Expression constraint = ((VariableDeclaration) declaration).getConstraint();
                    Expression newConstraint = constraint.substitute(oldVariable, newVariable);
                    newDeclaration.setConstraint(newConstraint);
                }
                else
                {
                    throw new UnsupportedOperationException();
                }
                body = expr.substitute(declaration.getVariable(), newDeclaration.getVariable());
                variables.remove(declaration);
                variables.add(newDeclaration);
            }
        }
        if(expr.equals(newVariable))
        {
            throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
        }

        Expression newExpression = body.substitute(oldVariable, newVariable);
        return new QuantifiedExpression(op, variables, newExpression);
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        if(oldExpression.equals(this))
        {
            return newExpression;
        }
        Expression expression = expr.replace(oldExpression, newExpression);
        return new QuantifiedExpression(op, variables, expression);
    }
}
