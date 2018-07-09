/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class TranslatorUtils
{
    private static int nameIndex = 0;

    private static int atomIndex = 0;

    private static int setIndex = 0;

    /**
     * Sanitize string s by replacing "\" with "_".
     * @param s
     * @return
     */
    public static String sanitizeName(String s) {
        return s.replaceAll("/", "_");
    }

    public static FunctionDeclaration generateAuxiliarySetNAtoms(Sort setSort, int n, Alloy2SMTTranslator translator)
    {
        List<Expression> expressions = declareNDistinctConstants(translator.atomSort, n, translator.smtProgram);

        FunctionDeclaration declaration = new FunctionDeclaration(getNewSet(), setSort);

        translator.smtProgram.addFunctionDeclaration(declaration);

        Expression set = new UnaryExpression(UnaryExpression.Op.SINGLETON, expressions.get(expressions.size() - 1));

        if(expressions.size() > 1)
        {
            List<Expression> atoms = new ArrayList<>();

            for(int i = 0; i < expressions.size() - 1; i++)
            {
                atoms.add(expressions.get(i));
            }

            atoms.add(set);

            set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atoms);
        }

        BinaryExpression equality = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.EQ, set);

        translator.smtProgram.addAssertion(new Assertion(equality));

        return declaration;
    }

    public static List<Expression> declareNDistinctConstants(Sort sort, int n, SMTProgram smtProgram)
    {
        List<Expression> expressions = new ArrayList<>();
        if(n > 0)
        {
            for (int i = 0; i < n; i++)
            {
                ConstantDeclaration constantDeclaration = new ConstantDeclaration(getNewAtom(), sort);
                MultiArityExpression makeTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantDeclaration.getConstantExpr());
                expressions.add(makeTuple);
                smtProgram.addConstantDeclaration(constantDeclaration);
            }

            if (n > 1)
            {
                MultiArityExpression distinct = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, expressions);
                smtProgram.addAssertion(new Assertion(distinct));
            }
        }
        else
        {
            throw new UnsupportedOperationException("Argument n should be greater than 0");
        }
        return expressions;
    }

    public static String getNewName()
    {
        nameIndex++;
        return "_x" + nameIndex;
    }

    public static String getNewAtom()
    {
        atomIndex ++;
        return "_a" + atomIndex;
    }

    public static String getNewSet()
    {
        setIndex ++;
        return "_S" + setIndex;
    }

    public static void reset()
    {
        nameIndex = 0;
        atomIndex = 0;
        setIndex  = 0;
    }
}
