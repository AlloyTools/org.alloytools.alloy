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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public abstract class AbstractTranslator
{
    // static members
    public final static String intSortName = "Int";
    public final static String boolSortName = "Bool";
    public final static String atom = "Atom";
    public final static String uninterpretedIntName = "UInt";
    public final static String uninterpretedIntValueName = "intValue";
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
    public final static FunctionDeclaration univAtom = new FunctionDeclaration("univAtom", setOfUnaryAtomSort, false);
    public final static FunctionDeclaration atomNone = new FunctionDeclaration("atomNone", setOfUnaryAtomSort, false);
    public final static FunctionDeclaration idenAtom = new FunctionDeclaration("idenAtom", setOfBinaryAtomSort, false);
    public final static FunctionDeclaration univInt = new FunctionDeclaration("univInt", setOfUninterpretedIntTuple, false);
    public final static FunctionDeclaration idenInt = new FunctionDeclaration("idenInt", setOfUninterpretedIntPairs, false);
    public final static UnaryExpression intUnivExpr = UnaryExpression.Op.UNIVSET.make(setOfUninterpretedIntTuple);
    public final static FunctionDeclaration uninterpretedIntValue = new FunctionDeclaration(uninterpretedIntValueName, uninterpretedInt, intSort, false);

    // special assertions
    public final static Assertion noneAssertion = new Assertion("", "Empty unary relation definition for Atom", BinaryExpression.Op.EQ.make(atomNone.getVariable(), UnaryExpression.Op.EMPTYSET.make(setOfUnaryAtomSort)));

    public final static Assertion univAssertion = new Assertion("", "Universe definition for Atom", BinaryExpression.Op.EQ.make(univAtom.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUnaryAtomSort)));

    public final static Assertion idenAtomAssertion = getIdentityRelation(atomSort, idenAtom);

    public final static Assertion univIntAssertion = new Assertion("", "Universe definition for UninterpretedInt", BinaryExpression.Op.EQ.make(univInt.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUninterpretedIntTuple)));

    public final static Assertion idenIntAssertion = getIdentityRelation(uninterpretedInt, idenInt);

    public final static Assertion intValueAssertion = getUninterpretedIntValueAssertion();

    // non static members
    public SmtScript smtScript;
    public Map<String, FunctionDeclaration> functionsMap;
    public Map<BinaryExpression.Op, FunctionDefinition> comparisonOperations;
    public Map<BinaryExpression.Op, Variable> arithmeticOperations;
    public Map<BigInteger, ConstantDeclaration> integerConstants;

    public void addFunction(FunctionDeclaration function)
    {
        this.functionsMap.put(function.getName(), function);
        this.smtScript.addFunction(function);
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

    public abstract SmtScript translate();

    public Expression handleIntConstant(Expression expression)
    {
        if(expression.getSort().equals(AbstractTranslator.intSortTuple))
        {
            Expression intConstant = ((MultiArityExpression) expression).getExpressions().get(0);
            ConstantDeclaration uninterpretedInt = this.getUninterpretedIntConstant((IntConstant) intConstant);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            return tuple;
        }
        if(expression.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            Expression intConstant = ((MultiArityExpression) ((UnaryExpression) expression).getExpression()).getExpressions().get(0);
            ConstantDeclaration uninterpretedInt = this.getUninterpretedIntConstant((IntConstant) intConstant);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple);
            return singleton;
        }
        return expression;
    }

    public ConstantDeclaration getUninterpretedIntConstant(IntConstant intConstant)
    {
        BigInteger value = new BigInteger(intConstant.getValue());
        if (integerConstants.containsKey(value))
        {
            return integerConstants.get(value);
        }

        ConstantDeclaration uninterpretedInt = new ConstantDeclaration(TranslatorUtils.getFreshName(AbstractTranslator.uninterpretedInt) + "_" + value.toString(),
                AbstractTranslator.uninterpretedInt, false);
        integerConstants.put(value, uninterpretedInt);
        smtScript.addConstantDeclaration(uninterpretedInt);
        Expression callExpression = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, uninterpretedInt.getVariable());
        Expression equality = BinaryExpression.Op.EQ.make(callExpression, intConstant);
        Assertion assertion = new Assertion("", "constant integer", equality);
        smtScript.addAssertion(assertion);
        return uninterpretedInt;
    }

    protected void translateSpecialAssertions()
    {
        this.smtScript.addAssertion(noneAssertion);
        this.smtScript.addAssertion(univAssertion);
        this.smtScript.addAssertion(univIntAssertion);
        this.smtScript.addAssertion(idenAtomAssertion);
        this.smtScript.addAssertion(idenIntAssertion);
        this.smtScript.addAssertion(intValueAssertion);
    }

    private static Assertion getUninterpretedIntValueAssertion()
    {
        // uninterpretedIntValue is injective function
        VariableDeclaration X = new VariableDeclaration("x", uninterpretedInt, false);
        VariableDeclaration Y = new VariableDeclaration("y", uninterpretedInt, false);
        Expression XEqualsY = BinaryExpression.Op.EQ.make(X.getVariable(), Y.getVariable());
        Expression notXEqualsY = UnaryExpression.Op.NOT.make(XEqualsY);

        Expression XValue = new FunctionCallExpression(uninterpretedIntValue, X.getVariable());
        Expression YValue = new FunctionCallExpression(uninterpretedIntValue, Y.getVariable());

        Expression XValueEqualsYValue = BinaryExpression.Op.EQ.make(XValue, YValue);
        Expression notXValueEqualsYValue = UnaryExpression.Op.NOT.make(XValueEqualsYValue);
        Expression implication = BinaryExpression.Op.IMPLIES.make(notXEqualsY, notXValueEqualsYValue);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implication, X, Y);

        return new Assertion("", uninterpretedIntValueName + " is injective", forAll);
    }

    private static Assertion getIdentityRelation(Sort sort, FunctionDeclaration identity)
    {
        // Axiom for identity relation
        VariableDeclaration a = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        VariableDeclaration b = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        MultiArityExpression tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, a.getVariable(), b.getVariable());

        BinaryExpression member = BinaryExpression.Op.MEMBER.make(tupleAB, identity.getVariable());

        BinaryExpression equals = BinaryExpression.Op.EQ.make(a.getVariable(), b.getVariable());

        BinaryExpression equiv = BinaryExpression.Op.EQ.make(member, equals);

        QuantifiedExpression forAll = QuantifiedExpression.Op.FORALL.make(equiv, a, b);

        Assertion assertion = new Assertion("", "Identity relation definition for " + identity.getName(), forAll);

        return assertion;
    }

    public SmtScript getSmtScript()
    {
        return smtScript;
    }

    public static List<FunctionDeclaration> getUninterpretedIntFunctions(SmtScript script)
    {
        List<FunctionDeclaration> functions = new ArrayList<>(Arrays.asList(AbstractTranslator.uninterpretedIntValue, AbstractTranslator.idenInt, AbstractTranslator.univInt));

        //ToDo: delete when alloy parser supports univInt
        List<FunctionDeclaration> univInt = script.getFunctions().stream()
                                                  .filter(f -> f.getName().equals("integer/univInt"))
                                                  .collect(Collectors.toList());
        functions.addAll(univInt);
        return functions;
    }

    public static List<Assertion> getUninterpretedIntAssertions(SmtScript script)
    {
        List<Assertion> assertions = new ArrayList<>();
        assertions.add(AbstractTranslator.univIntAssertion);
        assertions.add(AbstractTranslator.idenIntAssertion);
        assertions.add(AbstractTranslator.intValueAssertion);

        //ToDo: remove this when alloy parser supports univInt and idenInt
        List<Assertion> assertions1 = script.getAssertions().stream()
                                            .filter(a -> a.getComment().equals("integer/univInt = Int"))
                                            .collect(Collectors.toList());

        List<Assertion> assertions2 = script.getAssertions().stream()
                                            .filter(a -> a.getComment().equals("(all x,y | x = y <=> x -> y in (integer/univInt <: idenInt))"))
                                            .collect(Collectors.toList());

        List<Assertion> assertions3 = script.getAssertions().stream()
                                            .filter(a -> a.getComment().equals("universe") &&
                                                    a.getExpression().getComment().equals("integer/univInt = Int")
                                                   )
                                            .collect(Collectors.toList());

        List<Assertion> assertions4 = script.getAssertions().stream()
                                            .filter(a -> a.getComment().equals("identity") &&
                                                    a.getExpression().getComment().equals("(all x,y | x = y <=> x -> y in (integer/univInt <: idenInt))")
                                                   )
                                            .collect(Collectors.toList());

        assertions.addAll(assertions1);
        assertions.addAll(assertions2);
        assertions.addAll(assertions3);
        assertions.addAll(assertions4);

        return assertions;
    }

}
