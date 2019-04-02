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

        checkTypes();
    }

    @Override
    protected void checkTypes()
    {
        switch (op)
        {
            case OR:
            case AND:
            case IMPLIES:
                {
                    if (lhsExpr.getSort() != Alloy2SmtTranslator.boolSort)
                    {
                        throw new RuntimeException(String.format("Left expression sort '%1$s' is not boolean", lhsExpr.getSort()));
                    }
                    if (rhsExpr.getSort() != Alloy2SmtTranslator.boolSort)
                    {
                        throw new RuntimeException(String.format("Right expression sort '%1$s' is not boolean", rhsExpr.getSort()));
                    }
                } break;
            case PLUS:
            case MINUS:
            case MULTIPLY:
            case DIVIDE:
            case MOD:
            case GTE:
            case LTE:
            case GT:
            case LT:
            {
                if (lhsExpr.getSort() != Alloy2SmtTranslator.intSort)
                {
                    throw new RuntimeException(String.format("Left expression sort '%1$s' is not integer or  set of integers", lhsExpr.getSort()));
                }
                if (rhsExpr.getSort() != Alloy2SmtTranslator.intSort)
                {
                    throw new RuntimeException(String.format("Right expression sort '%1$s' is not integer or  set of integers", rhsExpr.getSort()));
                }
            } break;

            case EQ:
            case UNION:
            case INTERSECTION:
            case SETMINUS:
            case SUBSET:
            {
                if(! lhsExpr.getSort().equals(rhsExpr.getSort()))
                {
                    throw new RuntimeException(String.format("The sort of left expression sort '%1$s' is different than the sort of right expression '%2$s'", lhsExpr.getSort(), rhsExpr.getSort()));
                }
            } break;

            case MEMBER:
            {
                if(!(rhsExpr.getSort() instanceof  SetSort))
                {
                    throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set", rhsExpr.getSort()));
                }
                SetSort setSort = (SetSort) rhsExpr.getSort();

                if(!(lhsExpr.getSort().equals(setSort.elementSort)))
                {
                    throw new RuntimeException(String.format("The sort of left expression '%1$s' doesn't match the element sort of the right expression '%2$s'", lhsExpr.getSort(), setSort.elementSort));
                }
            } break;

            case JOIN:
            {
                if(!(lhsExpr.getSort() instanceof  SetSort &&
                        ((SetSort) lhsExpr.getSort()).elementSort instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort of left expression '%1$s' is not a set of tuples", lhsExpr.getSort()));
                }
                if(!(rhsExpr.getSort() instanceof  SetSort &&
                        ((SetSort) rhsExpr.getSort()).elementSort instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set of tuples", rhsExpr.getSort()));
                }

                TupleSort leftSort  = (TupleSort) ((SetSort) lhsExpr.getSort()).elementSort;
                TupleSort rightSort = (TupleSort) ((SetSort) rhsExpr.getSort()).elementSort;

                if(!(leftSort.elementSorts.get(leftSort.elementSorts.size() - 1).equals(rightSort.elementSorts.get(0))))
                {
                    throw new RuntimeException(String.format("The left and right sorts ('%1$s' and '%2$s') can't be joined", leftSort, rightSort));
                }
            } break;
            case PRODUCT:
            {
                if(!(lhsExpr.getSort() instanceof  SetSort &&
                        ((SetSort) lhsExpr.getSort()).elementSort instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort of left expression '%1$s' is not a set of tuples", lhsExpr.getSort()));
                }
                if(!(rhsExpr.getSort() instanceof  SetSort &&
                        ((SetSort) rhsExpr.getSort()).elementSort instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort of right expression '%1$s' is not a set of tuples", rhsExpr.getSort()));
                }
            } break;
            case TUPSEL:
            {
                if(!(lhsExpr instanceof IntConstant))
                {
                    throw new RuntimeException(String.format("The left expression '%1$s' is not a constant integer", lhsExpr));
                }
                if(!(rhsExpr.getSort() instanceof TupleSort))
                {
                    throw new RuntimeException(String.format("The sort of right expression '%1$s' is not tuple", rhsExpr.getSort()));
                }

                int index = Integer.parseInt(((IntConstant) lhsExpr).getValue());
                TupleSort sort = (TupleSort)rhsExpr.getSort();
                if (index >= sort.elementSorts.size() || index < 0)
                {
                    throw new RuntimeException(String.format("The index '%1$d' out of range", index));
                }
            } break;
            default:
                throw new UnsupportedOperationException();
        }
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
    public Sort getSort()
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

                Sort sort = new SetSort(new TupleSort(newSorts));

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

                Sort sort = new SetSort(new TupleSort(newSorts));
                return sort;
            }
            case TUPSEL:
            {
                int index = Integer.parseInt(((IntConstant) lhsExpr).getValue());
                TupleSort sort = (TupleSort)rhsExpr.getSort();
                return sort.elementSorts.get(index);
            }
            default:
                throw new UnsupportedOperationException();
        }
    }
}
