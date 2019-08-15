/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt;


import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class TranslatorUtils
{
    private static int freshNameIndex = 0;

    public static String sanitizeWithBars(Declaration declaration)
    {
        if(declaration.isOriginal())
        {
            // add extra space to separate original variables from generated ones
            return "|" + declaration.getName() + " |";
        }
        return declaration.getName();
    }

    public static String getFreshName(Sort sort)
    {
        freshNameIndex++;
        if(sort != null)
        {
            if (sort instanceof SetSort)
            {
                Sort elementSort = ((SetSort) sort).elementSort;
                if (elementSort instanceof TupleSort)
                {
                    int arity = ((TupleSort) elementSort).elementSorts.size();
                    if (arity > 1)
                    {
                        return "r" + arity + "." + freshNameIndex;
                    }
                }
                return "s" + "." + freshNameIndex;
            }

            if (sort instanceof TupleSort)
            {
                int arity = ((TupleSort) sort).elementSorts.size();
                if (arity > 1)
                {
                    return "t" + arity + "." + freshNameIndex;
                }
                Sort tupleSort = ((TupleSort) sort).elementSorts.get(0);
                if (tupleSort instanceof UninterpretedSort)
                {
                    UninterpretedSort uninterpretedSort = (UninterpretedSort) tupleSort;

                    if (uninterpretedSort.equals(AbstractTranslator.atomSort))
                    {
                        return "tA." + freshNameIndex;
                    }

                    if (uninterpretedSort.equals(AbstractTranslator.uninterpretedInt))
                    {
                        return "tU." + freshNameIndex;
                    }
                }
                return "t" + "." + freshNameIndex;
            }

            if (sort instanceof UninterpretedSort)
            {
                UninterpretedSort uninterpretedSort = (UninterpretedSort) sort;

                if (uninterpretedSort.equals(AbstractTranslator.atomSort))
                {
                    return "a." + freshNameIndex;
                }

                if (uninterpretedSort.equals(AbstractTranslator.uninterpretedInt))
                {
                    return "u." + freshNameIndex;
                }
            }
        }
        return "x." + freshNameIndex;
    }

    public static void reset()
    {
        freshNameIndex = 0;
    }

    public static Sort getSetSortOfAtomWithArity(int n)
    {
        List<Sort> elementSorts = new ArrayList<>();
        for (int i = 0; i < n; ++i)
        {
            elementSorts.add(AbstractTranslator.atomSort);
        }
        return new SetSort(new TupleSort(elementSorts));
    }

    public static Expression makeDistinct(Expression... exprs)
    {
        if (exprs == null)
        {
            throw new RuntimeException();
        }
        else if (exprs.length == 1)
        {
            return exprs[0];
        }
        else
        {
            return new MultiArityExpression(MultiArityExpression.Op.DISTINCT, exprs);
        }
    }

    public static Expression makeDistinct(List<Expression> exprs)
    {
        if (exprs == null)
        {
            throw new RuntimeException();
        }
        else if (exprs.isEmpty() || exprs.size() == 1)
        {
            return BoolConstant.True;
        }
        else
        {
            return MultiArityExpression.Op.DISTINCT.make(exprs);
        }
    }

    public static Expression getTuple(Declaration... elements)
    {
        List<Expression> expressions = Arrays.stream(elements)
                                             .map(Declaration::getVariable).collect(Collectors.toList());
        return MultiArityExpression.Op.MKTUPLE.make(expressions);
    }

    public static Expression getTuple(Expression... expressions)
    {
        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
    }

    public static int getInt(FunctionDefinition definition)
    {
        return getInt(definition.expression);
    }

    public static int getInt(Expression expression)
    {
        UnaryExpression unary = (UnaryExpression) expression;
        if (unary.getOP() == UnaryExpression.Op.EMPTYSET)
        {
            return 0; // zero is equivalent to an empty set
        }
        assert (UnaryExpression.Op.SINGLETON == unary.getOP());
        MultiArityExpression tuple = (MultiArityExpression) unary.getExpression();
        assert (MultiArityExpression.Op.MKTUPLE == tuple.getOp());
        IntConstant constant = (IntConstant) tuple.getExpressions().get(0);
        return Integer.parseInt(constant.getValue());
    }

    public static Set<Integer> getIntSet(FunctionDefinition definition)
    {
        return getIntSet(definition.getExpression());
    }

    public static Set<Integer> getIntSet(Expression expression)
    {
        if (expression instanceof UnaryExpression)
        {
            return new HashSet<>(Arrays.asList(getInt(expression)));
        }
        BinaryExpression binary = (BinaryExpression) expression;
        Set<Integer> set = new HashSet<>();
        assert (binary.getOp() == BinaryExpression.Op.UNION);
        set.addAll(getIntSet(binary.getLhsExpr()));
        set.addAll(getIntSet(binary.getRhsExpr()));
        return set;
    }

    public static Set<String> getAtomSet(FunctionDefinition definition)
    {
        return getAtomSet(definition.getExpression());
    }

    public static Set<String> getAtomSet(Expression expression)
    {
        if(expression instanceof UninterpretedConstant)
        {
            UninterpretedConstant constant  = (UninterpretedConstant) expression;
            return Collections.singleton(constant.getName());
        }
        if (expression instanceof UnaryExpression)
        {
            UnaryExpression unary = (UnaryExpression) expression;
            if (unary.getOP() == UnaryExpression.Op.EMPTYSET)
            {
                return new HashSet<>();
            }
            assert (UnaryExpression.Op.SINGLETON == unary.getOP());
            MultiArityExpression tuple = (MultiArityExpression) unary.getExpression();
            assert (MultiArityExpression.Op.MKTUPLE == tuple.getOp());
            UninterpretedConstant constant = (UninterpretedConstant) tuple.getExpressions().get(0);
            return new HashSet<>(Collections.singletonList(constant.getName()));
        }
        if(expression instanceof BinaryExpression)
        {
            BinaryExpression binary = (BinaryExpression) expression;
            Set<String> set = new HashSet<>();
            assert (binary.getOp() == BinaryExpression.Op.UNION);
            set.addAll(getAtomSet(binary.getLhsExpr()));
            set.addAll(getAtomSet(binary.getRhsExpr()));
            return set;
        }

        throw new UnsupportedOperationException("Not supported yet");
    }

    public static Set<List<String>> getRelation(FunctionDefinition definition)
    {
        if(!(definition.getSort() instanceof SetSort))
        {
            throw new UnsupportedOperationException(definition.getSort().toString());
        }
        SetSort setSort = (SetSort) definition.getSort();
        if(!(setSort.elementSort instanceof TupleSort))
        {
            throw new UnsupportedOperationException(setSort.elementSort.toString());
        }
        return getRelation(definition.getExpression());
    }

    public static Set<List<String>> getRelation(Expression expression)
    {
        if (expression instanceof UnaryExpression)
        {
            UnaryExpression unary = (UnaryExpression) expression;
            if (unary.getOP() == UnaryExpression.Op.EMPTYSET)
            {
                return new HashSet<>();
            }
            assert (UnaryExpression.Op.SINGLETON == unary.getOP());
            MultiArityExpression tupleExpression = (MultiArityExpression) unary.getExpression();
            assert (MultiArityExpression.Op.MKTUPLE == tupleExpression.getOp());
            List<String> tuple = new ArrayList<>();

            for (Expression expr: tupleExpression.getExpressions())
            {
                if(expr instanceof IntConstant)
                {
                    tuple.add(((IntConstant) expr).getValue());
                }
                else if(expr instanceof UninterpretedConstant)
                {
                    tuple.add(((UninterpretedConstant) expr).getName());
                }
                else
                {
                    throw new UnsupportedOperationException(expr.toString());
                }
            }
            return new HashSet<>(Collections.singletonList(tuple));
        }
        BinaryExpression binary = (BinaryExpression) expression;
        Set<List<String>> set = new HashSet<>();
        assert (binary.getOp() == BinaryExpression.Op.UNION);
        set.addAll(getRelation(binary.getLhsExpr()));
        set.addAll(getRelation(binary.getRhsExpr()));
        return set;
    }


    public static FunctionDefinition getFunctionDefinition(SmtModel smtModel, String name)
    {
        FunctionDefinition definition = (FunctionDefinition) smtModel
                .getFunctions().stream()
                .filter(f -> f.getName().equals(name)).findFirst().get();
        definition = smtModel.evaluateUninterpretedInt(definition);
        return definition;
    }

    public static String getFriendlyAtom(String uninterpretedConstant, String replacement)
    {
        return uninterpretedConstant.replaceFirst("@uc_Atom_", replacement);
    }

    public static String getOriginalName(String name)
    {
        return name.replaceAll("\\|", "");
    }
}
