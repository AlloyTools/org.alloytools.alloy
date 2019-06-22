/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.*;
import java.util.stream.Collectors;

public class MultiArityExpression extends Expression
{
    private final Op op;
    private final List<Expression> exprs;
    
    private MultiArityExpression(Op op, List<Expression> exprs)
    {
        this.op     = op;
        this.exprs  = exprs;

        if(this.exprs.stream().anyMatch(Objects::isNull))
        {
            throw new RuntimeException("One of the expression is null");
        }
        checkTypes();
    }

    public void checkTypes()
    {
        switch (op)
        {
            case MKTUPLE:
            {
                if(exprs.size() == 0)
                {
                    throw new RuntimeException("mkTuple operation requires at least one expression");
                }
                break;
            }
            case INSERT:
            {
                if(exprs.size() <= 1)
                {
                    throw new RuntimeException("Insert operation requires at least two expressions");
                }
                // the last expression should have a set sort
                Expression setExpression = exprs.get(exprs.size() - 1);
                if(!(setExpression.getSort() instanceof  SetSort))
                {
                    throw new RuntimeException(String.format("The expression '%1$s' has sort '%2S' which is not set",setExpression, setExpression.getSort()));
                }
                SetSort setSort = (SetSort) setExpression.getSort();

                // all remaining expressions should have the same sort of the elements of the set
                for (int i = 0; i < exprs.size() - 1; i++)
                {
                    Expression expression = exprs.get(i);
                    if(!(expression.getSort().equals(setSort.elementSort)))
                    {
                        throw new RuntimeException(String.format("The sort '%1$s' of expression '%2$s' doesn't match the elements sort '%3$s'", exprs.get(i).getSort(), expression , setSort.elementSort));
                    }
                }
            } break;
            case DISTINCT:
            {
                if(exprs.size() <= 1)
                {
                    throw new RuntimeException("distinct operation requires at least two expressions");
                }

                List<Sort> sorts = this.exprs.stream()
                                            .map(Expression::getSort).collect(Collectors.toList());
                Sort firstSort = sorts.get(0);
                for (int i = 1; i < sorts.size(); i++)
                {
                    if(!sorts.get(i).equals(firstSort))
                    {
                        throw new RuntimeException(String.format("Expressions of distinct operation do not have the same type:\n%s", sorts));
                    }
                }
            }break;
            default:
                throw new UnsupportedOperationException();
        }
    }

    public MultiArityExpression(Op op, Expression ... exprs)
    {
        this(op,  Arrays.asList(exprs));
    }    
    
    public Op getOp()
    {
        return this.op;
    }
    
    public List<Expression> getExpressions()
    {
        return this.exprs;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    public enum Op 
    {        
        MKTUPLE ("mkTuple"),
        INSERT ("insert"),
        DISTINCT ("distinct");

        private final String opStr;

        Op(String op)
        {
            this.opStr = op;
        }

        public MultiArityExpression make(List<Expression> exprs)
        {
            return new MultiArityExpression(this, exprs);
        }

       public static Op getOp(String operator)
       {
           switch (operator)
           {
               case "mkTuple"   : return MKTUPLE;
               case "insert"    : return INSERT;
               case "distinct"  : return DISTINCT;
               default:
                   throw new UnsupportedOperationException("Operator " + operator + " is not defined");
           }
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
        switch (op)
        {
            case MKTUPLE:
            {

                List<Sort> sorts = new ArrayList<>();
                for (Expression expr: exprs)
                {
                    sorts.add(expr.getSort());
                }
                return new TupleSort(sorts);
            }
            case INSERT:
            {
                // return the sort of the last element
                return exprs.get(exprs.size() - 1).getSort();
            }
            case DISTINCT: return AbstractTranslator.boolSort;
            default:
                throw new UnsupportedOperationException();
        }
    }
    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        List<Expression> expressions = new ArrayList<>();
        for (Expression expression : this.exprs)
        {
            expressions.add(expression.evaluate(functions));
        }
        return new MultiArityExpression(this.op, expressions);
    }

    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof MultiArityExpression))
        {
            return false;
        }
        MultiArityExpression multiArity = (MultiArityExpression) object;
        return op ==  multiArity.op &&
                exprs.equals(multiArity.exprs);
    }
    @Override
    public Expression substitute(Variable oldVariable, Variable newVariable)
    {
        List<Expression> newExpressions = new ArrayList<>();
        for (Expression expression: exprs)
        {
            if (expression.equals(newVariable))
            {
                throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
            }
            newExpressions.add(expression.substitute(oldVariable, newVariable));
        }
        return new MultiArityExpression(op, newExpressions);
    }

    @Override
    public Expression replace(Expression oldExpression, Expression newExpression)
    {
        if(oldExpression.equals(this))
        {
            return newExpression;
        }

        List<Expression> newExpressions = new ArrayList<>();
        for (Expression expression: exprs)
        {
            newExpressions.add(expression.replace(oldExpression, newExpression));
        }
        return new MultiArityExpression(op, newExpressions);
    }
}
