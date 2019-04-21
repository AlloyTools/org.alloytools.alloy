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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class UnaryExpression extends Expression
{    
    private final Op op;
    private final Expression expr;
    
    public UnaryExpression(Op op, Expression expr)
    {
        this.op     = op;
        if(expr == null)
        {
            throw new RuntimeException("Expression is null");
        }
        this.expr   = expr;
        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        switch (op)
        {
            case NOT:
            {
                if (expr.getSort() != AbstractTranslator.boolSort)
                {
                    throw new RuntimeException(String.format("Expression sort '%1$s' is not boolean", expr.getSort()));
                }
            } break;
            case COMPLEMENT:
            {
                if(!(expr.getSort() instanceof  SetSort))
                {
                    throw new RuntimeException(String.format("The sort '%1$s' of expression '%2$s' is not a set", expr.getSort(), expr));
                }
            } break;
            case TRANSPOSE:
            case TCLOSURE:
            {
                if(!(expr.getSort() instanceof  SetSort &&
                        ((SetSort) expr.getSort()).elementSort instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort '%1$s' of expression '%2$s' is not a set of tuples", expr.getSort(), expr));
                }
            } break;
            case EMPTYSET:
            case UNIVSET:
            {
                if(!(expr instanceof Sort))
                {
                    throw new RuntimeException(String.format("Expected a set sort. Found '%1$s'", expr));
                }
            } break;
            case SINGLETON: break;
            default:
                throw new UnsupportedOperationException();
        }
    }

    public Op getOP() 
    {
        return this.op;
    }
    
    public Expression getExpression() 
    {
        return this.expr;
    }
    
    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
    
    public enum Op 
    {	        
        NOT ("not"),
        COMPLEMENT ("complement"),
        TRANSPOSE ("transpose"),
        TCLOSURE("tclosure"),
        SINGLETON("singleton"),
        UNIVSET("as univset"),
        EMPTYSET("as emptyset");

        private final String opStr;

        Op(String str)
        {
            this.opStr = str;
        }

        public static Op getOp(String operator)
        {
            switch (operator)
            {
                case"not"           : return NOT;
                case "complement"   : return COMPLEMENT;
                case "transpose"    : return TRANSPOSE;
                case "tclosure"     : return TCLOSURE;
                case "singleton"    : return SINGLETON;
                case "as univset"   : return UNIVSET;
                case "as emptyset"  : return EMPTYSET;
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
        switch (op) {
            case NOT:
                return AbstractTranslator.boolSort;
            case COMPLEMENT:
                return expr.getSort();
            case TRANSPOSE: {
                // type checking is handled during construction
                TupleSort oldSort = (TupleSort) ((SetSort) expr.getSort()).elementSort;
                List<Sort> reverse = new ArrayList<>();
                for (int i = oldSort.elementSorts.size() - 1; i >= 0; i--) {
                    reverse.add(oldSort.elementSorts.get(i));
                }
                SetSort sort = new SetSort(new TupleSort(reverse));
                return sort;
            }
            case TCLOSURE:
                return expr.getSort();
            case SINGLETON:
                return new SetSort(expr.getSort());
            case EMPTYSET:
                return expr.getSort();
            case UNIVSET:
                return expr.getSort();
            default:
                throw new UnsupportedOperationException();
        }
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        if(op == Op.EMPTYSET)
        {
            if(expr.equals(AbstractTranslator.setOfUninterpretedIntTuple))
            {
                return new UnaryExpression(op, AbstractTranslator.setOfIntSortTuple);
            }
            else
            {
                return this;
            }
        }
        Expression expression = this.expr.evaluate(functions);
        return new UnaryExpression(this.op, expression);
    }
    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof UnaryExpression))
        {
            return false;
        }
        UnaryExpression unaryObject = (UnaryExpression) object;
        return op ==  unaryObject.op &&
                expr.equals(unaryObject.expr);
    }
}
