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
  public final static SmtUnaryExpr intUnivExpr = SmtUnaryExpr.Op.UNIVSET.make(setOfUninterpretedIntTuple);
  public final static FunctionDeclaration uninterpretedIntValue = new FunctionDeclaration(uninterpretedIntValueName, uninterpretedInt, intSort, false);

  // special assertions
  public final static Assertion noneAssertion = new Assertion("", "Empty unary relation definition for Atom", SmtBinaryExpr.Op.EQ.make(atomNone.getVariable(), SmtUnaryExpr.Op.EMPTYSET.make(setOfUnaryAtomSort)));

  public final static Assertion univAssertion = new Assertion("", "Universe definition for Atom", SmtBinaryExpr.Op.EQ.make(univAtom.getVariable(), SmtUnaryExpr.Op.UNIVSET.make(setOfUnaryAtomSort)));

  public final static Assertion idenAtomAssertion = getIdentityRelation(atomSort, idenAtom);

  public final static Assertion univIntAssertion = new Assertion("", "Universe definition for UninterpretedInt", SmtBinaryExpr.Op.EQ.make(univInt.getVariable(), SmtUnaryExpr.Op.UNIVSET.make(setOfUninterpretedIntTuple)));

  public final static Assertion idenIntAssertion = getIdentityRelation(uninterpretedInt, idenInt);

  public final static Assertion intValueAssertion = getUninterpretedIntValueAssertion();

  // non static members
  public SmtScript smtScript;
  public Map<String, FunctionDeclaration> functionsMap;
  public Map<SmtBinaryExpr.Op, FunctionDefinition> comparisonOperations;
  public Map<SmtBinaryExpr.Op, Variable> arithmeticOperations;

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

  public SmtExpr handleIntConstant(SmtExpr smtExpr)
  {
    if (smtExpr.getSort().equals(AbstractTranslator.intSortTuple))
    {
      SmtExpr intConstant = ((SmtMultiArityExpr) smtExpr).getExprs().get(0);
      FunctionDeclaration uninterpretedInt = this.getUninterpretedIntConstant((IntConstant) intConstant);
      SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, uninterpretedInt.getVariable());
      return tuple;
    }
    if (smtExpr.getSort().equals(AbstractTranslator.setOfIntSortTuple))
    {
      SmtExpr intConstant = ((SmtMultiArityExpr) ((SmtUnaryExpr) smtExpr).getExpr()).getExprs().get(0);
      FunctionDeclaration uninterpretedInt = this.getUninterpretedIntConstant((IntConstant) intConstant);
      SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, uninterpretedInt.getVariable());
      SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(tuple);
      return singleton;
    }
    return smtExpr;
  }

  public FunctionDeclaration getUninterpretedIntConstant(IntConstant intConstant)
  {
    BigInteger value = new BigInteger(intConstant.getValue());
    Map<BigInteger, FunctionDeclaration> integerConstants = smtScript.getIntegerConstants();
    if (smtScript.getIntegerConstants().containsKey(value))
    {
      return integerConstants.get(value);
    }

    FunctionDeclaration uninterpretedInt = new FunctionDeclaration(TranslatorUtils.getFreshName(AbstractTranslator.uninterpretedInt) + "_" + value.toString(),
        AbstractTranslator.uninterpretedInt, false);
    smtScript.putIntegerConstant(value, uninterpretedInt);
    SmtExpr callSmtExpr = new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, uninterpretedInt.getVariable());
    SmtExpr equality = SmtBinaryExpr.Op.EQ.make(callSmtExpr, intConstant);
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
    SmtVariable X = new SmtVariable("x", uninterpretedInt, false);
    SmtVariable Y = new SmtVariable("y", uninterpretedInt, false);
    SmtExpr XEqualsY = SmtBinaryExpr.Op.EQ.make(X.getVariable(), Y.getVariable());
    SmtExpr notXEqualsY = SmtUnaryExpr.Op.NOT.make(XEqualsY);

    SmtExpr XValue = new SmtCallExpr(uninterpretedIntValue, X.getVariable());
    SmtExpr YValue = new SmtCallExpr(uninterpretedIntValue, Y.getVariable());

    SmtExpr XValueEqualsYValue = SmtBinaryExpr.Op.EQ.make(XValue, YValue);
    SmtExpr notXValueEqualsYValue = SmtUnaryExpr.Op.NOT.make(XValueEqualsYValue);
    SmtExpr implication = SmtBinaryExpr.Op.IMPLIES.make(notXEqualsY, notXValueEqualsYValue);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implication, X, Y);

    return new Assertion("", uninterpretedIntValueName + " is injective", forAll);
  }

  private static Assertion getIdentityRelation(Sort sort, FunctionDeclaration identity)
  {
    // Axiom for identity relation
    SmtVariable a = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

    SmtVariable b = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);

    SmtMultiArityExpr tupleAB = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, a.getVariable(), b.getVariable());

    SmtBinaryExpr member = SmtBinaryExpr.Op.MEMBER.make(tupleAB, identity.getVariable());

    SmtBinaryExpr equals = SmtBinaryExpr.Op.EQ.make(a.getVariable(), b.getVariable());

    SmtBinaryExpr equiv = SmtBinaryExpr.Op.EQ.make(member, equals);

    SmtQtExpr forAll = SmtQtExpr.Op.FORALL.make(equiv, a, b);

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
                                                a.getSmtExpr().getComment().equals("integer/univInt = Int")
                                               )
                                        .collect(Collectors.toList());

    List<Assertion> assertions4 = script.getAssertions().stream()
                                        .filter(a -> a.getComment().equals("identity") &&
                                                a.getSmtExpr().getComment().equals("(all x,y | x = y <=> x -> y in (integer/univInt <: idenInt))")
                                               )
                                        .collect(Collectors.toList());

    assertions.addAll(assertions1);
    assertions.addAll(assertions2);
    assertions.addAll(assertions3);
    assertions.addAll(assertions4);

    return assertions;
  }

}
