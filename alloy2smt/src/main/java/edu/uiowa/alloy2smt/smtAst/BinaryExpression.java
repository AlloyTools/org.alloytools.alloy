/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;

import java.util.ArrayList;
import java.util.List;

public class BinaryExpression extends Expression
{
    private final Op            op;
    private final Expression    lhsExpr;
    private final Expression    rhsExpr;
    
    public BinaryExpression(Expression lhsExpr, Op op, Expression rhsExpr) 
    {
        this.op         = op;
        if(lhsExpr == null)
        {
            throw new RuntimeException("Left expression is null");
        }
        this.lhsExpr    = lhsExpr;
        if(rhsExpr == null)
        {
            throw new RuntimeException("Right expression is null");
        }
        this.rhsExpr    = rhsExpr;

    }
    
    public Expression getLhsExpr() 
    {
        return this.lhsExpr;
    }
    
    public Expression getRhsExpr() 
    {
        return this.rhsExpr;
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
        OR ("or"),
        AND ("and"),  
        IMPLIES ("=>"),        
        PLUS ("+"),
        MINUS ("-"),
        MULTIPLY ("*"),
        DIVIDE ("/"),
        MOD ("mod"),
        EQ ("="),
        NEQ ("<>"), //ToDo: clean this up
        GTE (">="),
        LTE ("<="),
        GT (">"),
        LT ("<"),        
        UNION ("union"),
        INTERSECTION ("intersection"),
        SETMINUS ("setminus"),        
        MEMBER ("member"),
        SUBSET ("subset"),
        JOIN ("join"),
        PRODUCT ("product"),
        TUPSEL ("tupSel");

        private final String opStr;

        Op(String op)
        {
            this.opStr = op;
        }

        public static Op getOp(String operator)
        {
            switch (operator)
            {
                case"or"            : return OR;
                case "and"          : return AND;
                case "=>"           : return IMPLIES;
                case "+"            : return PLUS;
                case "-"            : return MINUS;
                case "*"            : return MULTIPLY;
                case "/"            : return DIVIDE;
                case "mod"          : return MOD;
                case "="            : return EQ;
                case ">="           : return GTE;
                case "<="           : return LTE;
                case ">"            : return GT;
                case "<"            : return LT;
                case "union"        : return UNION;
                case "intersection" : return INTERSECTION;
                case "setminus"     : return SETMINUS;
                case "member"       : return MEMBER;
                case "subset"       : return SUBSET;
                case "join"         : return JOIN;
                case "product"      : return PRODUCT;
                case "tupSel"       : return TUPSEL;
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
    public Sort getSort() throws Exception
    {
        switch (op)
        {
            case OR: return Alloy2SmtTranslator.boolSort;
            case AND: return Alloy2SmtTranslator.boolSort ;
            case IMPLIES: return Alloy2SmtTranslator.boolSort;
            case PLUS: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case MINUS: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case MULTIPLY: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case DIVIDE: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case MOD: return lhsExpr.getSort() instanceof IntSort? Alloy2SmtTranslator.intSort: Alloy2SmtTranslator.setOfUnaryIntSort;
            case EQ: return Alloy2SmtTranslator.boolSort;
            case GTE: return Alloy2SmtTranslator.boolSort;
            case LTE: return Alloy2SmtTranslator.boolSort;
            case GT: return Alloy2SmtTranslator.boolSort;
            case LT: return Alloy2SmtTranslator.boolSort;
            case UNION: return lhsExpr.getSort();
            case INTERSECTION: return lhsExpr.getSort();
            case SETMINUS: return lhsExpr.getSort();
            case MEMBER: return Alloy2SmtTranslator.boolSort;
            case SUBSET: return Alloy2SmtTranslator.boolSort;
            case JOIN:
            {
                // type checking is handled during construction

                TupleSort leftSort  = (TupleSort) ((SetSort) lhsExpr.getSort()).elementSort;
                TupleSort rightSort = (TupleSort) ((SetSort) rhsExpr.getSort()).elementSort;

                // the join sorts should match
                assert(leftSort.elementSorts.get(leftSort.elementSorts.size() - 1) ==
                        rightSort.elementSorts.get(0));

                List<Sort> newSorts = new ArrayList<>();
                for (int i = 0; i < leftSort.elementSorts.size() - 1; i++)
                {
                    newSorts.add(leftSort.elementSorts.get(i));
                }

                for (int i = 1; i < rightSort.elementSorts.size(); i++)
                {
                    newSorts.add(rightSort.elementSorts.get(i));
                }

                Sort sort = new TupleSort(newSorts);

                return sort;
            }
            case PRODUCT:
            {
                // type checking is handled during construction

                TupleSort leftSort  = (TupleSort) ((SetSort) lhsExpr.getSort()).elementSort;
                TupleSort rightSort = (TupleSort) ((SetSort) rhsExpr.getSort()).elementSort;

                List<Sort> newSorts = new ArrayList<>();
                newSorts.addAll(leftSort.elementSorts);
                newSorts.addAll(rightSort.elementSorts);

                Sort sort = new TupleSort(newSorts);
                return sort;
            }
            case TUPSEL: throw new UnsupportedOperationException("TUPSEL");
            default:
                throw new UnsupportedOperationException();
        }
    }
}
