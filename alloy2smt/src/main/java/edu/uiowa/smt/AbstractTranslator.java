/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.*;

import java.math.BigInteger;
import java.util.Map;

public abstract class AbstractTranslator
{
    // static members
    public final static String intSortName = "Int";
    public final static String atom = "Atom";
    public final static String uninterpretedIntName = "UninterpretedInt";
    public final static String uninterpretedIntValueName = "uninterpretedIntValue";
    public final static String plus = "PLUS";
    public final static String minus = "MINUS";
    public final static String multiply = "MUL";
    public final static String divide = "DIV";
    public final static String mod = "MOD";
    public final static IntSort intSort = IntSort.getInstance();
    public final static TupleSort intSortTuple = new TupleSort(intSort);
    public final static SetSort setOfIntSortTuple = new SetSort(intSortTuple);
    public final static BoolSort boolSort = BoolSort.getInstance();
    public final static UninterpretedSort atomSort = new UninterpretedSort(atom);
    public final static UninterpretedSort uninterpretedInt = new UninterpretedSort(uninterpretedIntName);
    public final static TupleSort uninterpretedIntTuple = new TupleSort(uninterpretedInt);
    public final static SetSort setOfUninterpretedIntTuple = new SetSort(uninterpretedIntTuple);
    public final static SetSort setOfUninterpretedIntPairs = new SetSort(new TupleSort(uninterpretedInt, uninterpretedInt));
    public final static TupleSort unaryAtomSort = new TupleSort(atomSort);
    public final static TupleSort binaryAtomSort = new TupleSort(atomSort, atomSort);
    public final static TupleSort ternaryIntSort = new TupleSort(uninterpretedInt, uninterpretedInt, uninterpretedInt);
    public final static SetSort setOfUnaryAtomSort = new SetSort(unaryAtomSort);
    public final static SetSort setOfBinaryAtomSort = new SetSort(binaryAtomSort);
    public final static SetSort setOfTernaryIntSort = new SetSort(ternaryIntSort);
    public final static FunctionDeclaration atomUniverse = new FunctionDeclaration("atomUniverse", setOfUnaryAtomSort);
    public final static FunctionDeclaration atomNone = new FunctionDeclaration("atomNone", setOfUnaryAtomSort);
    public final static FunctionDeclaration atomIdentity = new FunctionDeclaration("atomIdentity", setOfBinaryAtomSort);
    //ToDo: review intUniv
    public final static FunctionDeclaration intUniv = new FunctionDeclaration("intUniv", setOfUninterpretedIntTuple);
    public final static UnaryExpression intUnivExpr = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUninterpretedIntTuple);
    public final static FunctionDeclaration uninterpretedIntValue = new FunctionDeclaration(uninterpretedIntValueName, uninterpretedInt, intSort);
    public final static String CHECK_SAT = "(check-sat)";
    public final static String GET_MODEL = "(get-model)";
    public final static String PUSH = "(push 1)";
    public final static String POP = "(pop 1)";

    // non static members
    public SmtProgram smtProgram;
    public Map<String, FunctionDeclaration> functionsMap;
    public Map<BinaryExpression.Op, FunctionDefinition> comparisonOperations;
    public Map<BinaryExpression.Op, Variable> arithmeticOperations;
    public Map<BigInteger, ConstantDeclaration> integerConstants;

    public void addFunction(FunctionDeclaration function)
    {
        this.functionsMap.put(function.getName(), function);
        this.smtProgram.addFunction(function);
    }

    public FunctionDeclaration getFunction(String functionName)
    {
        FunctionDeclaration function = functionsMap.get(functionName);
        if (function == null)
        {
            throw new RuntimeException("Function " + functionName + " is not found.");
        }
        return function;
    }

    public abstract SmtProgram translate();

    public Expression handleIntConstant(Expression expression)
    {
        Expression intConstant = ((MultiArityExpression) ((UnaryExpression) expression).getExpression()).getExpressions().get(0);
        ConstantDeclaration uninterpretedInt = this.getUninterpretedIntConstant((IntConstant) intConstant);
        Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
        expression = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return expression;
    }

    public ConstantDeclaration getUninterpretedIntConstant(IntConstant intConstant)
    {
        BigInteger value = new BigInteger(intConstant.getValue());
        if (integerConstants.containsKey(value))
        {
            return integerConstants.get(value);
        }

        ConstantDeclaration uninterpretedInt = new ConstantDeclaration(TranslatorUtils.getNewAtomName(), AbstractTranslator.uninterpretedInt);
        integerConstants.put(value, uninterpretedInt);
        smtProgram.addConstantDeclaration(uninterpretedInt);
        Expression callExpression = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, uninterpretedInt.getVariable());
        Expression equality = new BinaryExpression(callExpression, BinaryExpression.Op.EQ, intConstant);
        Assertion assertion = new Assertion("constant integer", equality);
        smtProgram.addAssertion(assertion);
        return uninterpretedInt;
    }
}
