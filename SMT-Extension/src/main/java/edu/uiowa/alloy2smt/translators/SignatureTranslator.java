/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.SmtEnv;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

public class SignatureTranslator
{

  private final Alloy2SmtTranslator translator;
  private final FieldTranslator fieldTranslator;

  private List<Map.Entry<Sig, Expr>> translatedSigFacts = new ArrayList<>();

  public SignatureTranslator(Alloy2SmtTranslator translator)
  {
    this.translator = translator;
    this.fieldTranslator = new FieldTranslator(translator);
  }

  private void translateSignatureHierarchies()
  {
    for (Sig sig : translator.reachableSigs)
    {
      if (sig instanceof Sig.PrimSig)
      {
        Sig.PrimSig primSig = (Sig.PrimSig) sig;

        if (primSig.isAbstract != null)
        {
          SafeList<Sig.PrimSig> children = primSig.children();
          if (children.size() > 0)
          {
            SmtExpr left = translator.signaturesMap.get(sig).getVariable();
            SmtExpr union = translator.signaturesMap.get(children.get(0)).getVariable();

            for (int i = 1; i < children.size(); i++)
            {
              SmtExpr smtExpr = translator.signaturesMap.get(children.get(i)).getVariable();
              union = SmtBinaryExpr.Op.UNION.make(union, smtExpr);
            }

            SmtBinaryExpr equality = SmtBinaryExpr.Op.EQ.make(left, union);
            List<Pos> positions = children.makeCopy().stream()
                                          .map(s -> s.pos).collect(Collectors.toList());
            Assertion isAbstract = AlloyUtils.getAssertion(positions, "abstract " + primSig.toString(), equality);
            translator.smtScript.addAssertion(isAbstract);
          }
        }
      }
    }

    if (translator.topLevelSigs.size() > 0)
    {
      // The union of all top-level sigs equals to the universe
      SmtExpr unionTopSigExprs = translator.signaturesMap.get(translator.topLevelSigs.get(0)).getVariable();

      for (int i = 1; i < translator.topLevelSigs.size(); ++i)
      {
        unionTopSigExprs = SmtBinaryExpr.Op.UNION.make(unionTopSigExprs, translator.signaturesMap.get(translator.topLevelSigs.get(i)).getVariable());
      }
      SmtExpr equal = SmtBinaryExpr.Op.EQ.make(unionTopSigExprs, translator.univAtom.getVariable());
      List<Pos> positions = translator.topLevelSigs.stream().map(s -> s.pos).collect(Collectors.toList());
      Assertion assertion = AlloyUtils.getAssertion(positions, "atomUniv is the union of top level signatures", equal);
      translator.smtScript.addAssertion(assertion);

      // Top-level sigs are mutually disjoint
      if (translator.topLevelSigs.size() > 1)
      {
        for (int i = 0; i < translator.topLevelSigs.size() - 1; ++i)
        {
          SmtExpr fstSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(i)).getVariable();

          for (int j = i + 1; j < translator.topLevelSigs.size(); ++j)
          {
            SmtExpr sndSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(j)).getVariable();
            SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(fstSigExpr, sndSigExpr);
            SmtExpr disjoint = SmtBinaryExpr.Op.EQ.make(intersect, AbstractTranslator.atomNone.getVariable());
            assertion = AlloyUtils.getAssertion(positions,
                "Top level signatures are disjoint", disjoint);
            translator.smtScript.addAssertion(assertion);
          }
        }
      }

    }
  }

  private void translateDisjointSignatures(List<Sig.PrimSig> signatures)
  {
    for (int i = 0; i < signatures.size(); i++)
    {
      Sig signature = signatures.get(i);
      SmtExpr left = translator.signaturesMap.get(signature).getVariable();

      for (int j = i + 1; j < signatures.size(); j++)
      {
        SmtExpr right = translator.signaturesMap.get(signatures.get(j)).getVariable();
        SmtBinaryExpr disjoint = SmtBinaryExpr.Op.INTERSECTION.make(left, right);
        SmtBinaryExpr equality = SmtBinaryExpr.Op.EQ.make(disjoint, translator.atomNone.getVariable());

        List<Pos> positions = Arrays.asList(signature.pos, signatures.get(j).pos);
        Assertion assertion = AlloyUtils.getAssertion(positions, "Disjoint signatures", equality);
        translator.smtScript.addAssertion(assertion);
      }
      // recursively add disjoint constraints to children
      if (signature instanceof Sig.PrimSig)
      {
        Sig.PrimSig primSig = (Sig.PrimSig) signature;
        List<Sig.PrimSig> children = primSig.children().makeCopy()
                                            .stream().collect(Collectors.toList());
        translateDisjointSignatures(children);
      }
    }
  }

  private void collectReachableSigs()
  {
    for (Sig sig : translator.alloyModel.getAllReachableSigs())
    {
      if (sig.builtin)
      {
        continue;
      }
      if (sig.isTopLevel())
      {
        translator.topLevelSigs.add(sig);
      }
      translator.reachableSigs.add(sig);
    }
  }

  private void translateSignatures()
  {
    for (Sig sig : translator.reachableSigs)
    {
      if (sig.type().is_int())
      {
        FunctionDeclaration functionDeclaration = declareUnaryIntFunction(sig.toString(), true);
        translator.signaturesMap.put(sig, functionDeclaration);
      }
      else
      {
        FunctionDeclaration functionDeclaration = declareUnaryAtomFunction(sig.toString(), true);
        translator.signaturesMap.put(sig, functionDeclaration);
      }
    }

    for (Sig sig : translator.reachableSigs)
    {
      FunctionDeclaration functionDeclaration = translator.signaturesMap.get(sig);

      // if sig extends another signature
      if (!sig.isTopLevel())
      {
        translateSigSubsetParent(sig, functionDeclaration);
      }

      if (sig.isOne != null)
      {
        translateSignatureOneMultiplicity(sig);
      }
      else if (sig.isLone != null)
      {
        translateSignatureLoneMultiplicity(sig);
      }
      else if (sig.isSome != null)
      {
        translateSignatureSomeMultiplicity(sig);
      }

      for (Expr expr : sig.getFacts())
      {
        translator.sigFacts.put(sig, expr);
      }
    }

    List<Sig.PrimSig> primSigs = translator.topLevelSigs
        .stream().map(s -> (Sig.PrimSig) s).collect(Collectors.toList());
    translateDisjointSignatures(primSigs);
  }

  private void translateSignatureOneMultiplicity(Sig sig)
  {
    SmtExpr expr;
    FunctionDeclaration constDecl;
    Boolean isInt = sig.type().is_int();

    FunctionDeclaration signature = translator.signaturesMap.get(sig);

    if (isInt)
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.uninterpretedInt);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.uninterpretedInt, false);
    }
    else
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.atomSort);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.atomSort, false);
    }
    expr = AlloyUtils.mkSingletonOutOfTuple(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, constDecl.getVariable()));
    translator.smtScript.addFunction(constDecl);

    SmtBinaryExpr subset = SmtBinaryExpr.Op.EQ.make(signature.getVariable(), expr);
    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos), "one " + sig.label, subset);
    translator.smtScript.addAssertion(assertion);
  }

  private void translateSignatureLoneMultiplicity(Sig sig)
  {
    SmtExpr expr;
    FunctionDeclaration constDecl;
    Boolean isInt = sig.type().is_int();
    FunctionDeclaration signature = translator.signaturesMap.get(sig);

    if (isInt)
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.uninterpretedInt);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.uninterpretedInt, false);
      expr = AlloyUtils.mkSingletonOutOfTuple(new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, constDecl.getVariable()));
    }
    else
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.atomSort);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.atomSort, false);
      expr = AlloyUtils.mkSingletonOutOfTuple(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, constDecl.getVariable()));
    }
    translator.smtScript.addFunction(constDecl);

    SmtBinaryExpr subset = SmtBinaryExpr.Op.SUBSET.make(signature.getVariable(), expr);
    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos), "lone " + sig.label, subset);
    translator.smtScript.addAssertion(assertion);
  }

  private void translateSignatureSomeMultiplicity(Sig sig)
  {
    SmtExpr expr;
    FunctionDeclaration constDecl;
    Boolean isInt = sig.type().is_int();
    FunctionDeclaration signature = translator.signaturesMap.get(sig);

    if (isInt)
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.uninterpretedInt);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.uninterpretedInt, false);
      expr = AlloyUtils.mkSingletonOutOfTuple(new SmtCallExpr(AbstractTranslator.uninterpretedIntValue, constDecl.getVariable()));
    }
    else
    {
      String name = TranslatorUtils.getFreshName(AbstractTranslator.atomSort);
      constDecl = new FunctionDeclaration(name, AbstractTranslator.atomSort, false);
      expr = AlloyUtils.mkSingletonOutOfTuple(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, constDecl.getVariable()));
    }
    translator.smtScript.addFunction(constDecl);

    SmtBinaryExpr subset = SmtBinaryExpr.Op.SUBSET.make(expr, signature.getVariable());
    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos), "some " + sig.label, subset);
    translator.smtScript.addAssertion(assertion);
  }


  private void translateSigSubsetParent(Sig sig, FunctionDeclaration functionDeclaration)
  {
    if (sig instanceof Sig.PrimSig)
    {
      Sig parent = ((Sig.PrimSig) sig).parent;
      FunctionDeclaration parentDeclaration = translator.signaturesMap.get(parent);
      SmtBinaryExpr subsetExpression = SmtBinaryExpr.Op.SUBSET.make(functionDeclaration.getVariable(), parentDeclaration.getVariable());
      Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos),
          sig.label + " in " + parent.label, subsetExpression);
      translator.smtScript.addAssertion(assertion);
    }
    else
    {
      List<Sig> parents = ((Sig.SubsetSig) sig).parents;

      if (parents.size() == 1)
      {
        Sig parentSig = parents.get(0);

        // We consider parentSig as int
//                if(parentSig == Sig.SIGINT && !translator.signaturesMap.containsKey(parentSig))
//                {
//                    declareIntSig();
//                }
        if (parentSig != Sig.SIGINT)
        {
          FunctionDeclaration parentDeclaration = translator.signaturesMap.get(parentSig);
          SmtBinaryExpr subset = SmtBinaryExpr.Op.SUBSET.make(functionDeclaration.getVariable(), parentDeclaration.getVariable());
          Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos),
              sig.label + " in " + parentSig.label, subset);
          translator.smtScript.addAssertion(assertion);
        }
      }
      else
      {
        SmtExpr left = translator.signaturesMap.get(parents.get(0)).getVariable();
        SmtExpr right = translator.signaturesMap.get(parents.get(1)).getVariable();
        SmtBinaryExpr union = SmtBinaryExpr.Op.UNION.make(left, right);

        for (int i = 2; i < parents.size(); i++)
        {
          SmtExpr smtExpr = translator.signaturesMap.get(parents.get(i)).getVariable();
          union = SmtBinaryExpr.Op.UNION.make(union, smtExpr);
        }

        SmtBinaryExpr subset = SmtBinaryExpr.Op.SUBSET.make(functionDeclaration.getVariable(), union);
        Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sig.pos),
            sig.toString(), subset);
        translator.smtScript.addAssertion(assertion);
      }
    }
  }

  private FunctionDeclaration declareUnaryAtomFunction(String varName, boolean isOriginal)
  {
    FunctionDeclaration declaration = null;
    if (varName != null)
    {
      declaration = new FunctionDeclaration(varName, translator.setOfUnaryAtomSort, isOriginal);
      translator.smtScript.addFunction(declaration);
    }
    return declaration;
  }

  private FunctionDeclaration declareUnaryIntFunction(String varName, boolean isOriginal)
  {
    FunctionDeclaration declaration = null;
    if (varName != null)
    {
      declaration = new FunctionDeclaration(varName, translator.setOfUninterpretedIntTuple, isOriginal);
      translator.smtScript.addFunction(declaration);
    }
    return declaration;
  }

  public void translateSigs()
  {
    collectReachableSigs();
    translateSignatures();
    translateSignatureHierarchies();
    this.fieldTranslator.translateFields();
  }

  void translateSpecialSigFacts()
  {
    // Translate facts on signatures
    for (Map.Entry<Sig, Expr> sigFact : translator.sigFacts.entrySet())
    {
      SmtEnv smtEnv = new SmtEnv();
      Expr expr = sigFact.getValue();

      // handle total order operator differently
      if (expr instanceof ExprUnary &&
          ((ExprUnary) expr).sub instanceof ExprList &&
          ((ExprList) ((ExprUnary) expr).sub).op == ExprList.Op.TOTALORDER)
      {
        translateTotalOrder(sigFact.getKey(), ((ExprList) ((ExprUnary) expr).sub), smtEnv);
        this.translatedSigFacts.add(sigFact);
      }
    }
  }


  void translateSigFacts()
  {
    // Translate facts on signatures
    for (Map.Entry<Sig, Expr> sigFact : translator.sigFacts.entrySet())
    {
      // ignore already translated signature facts
      if (this.translatedSigFacts.contains(sigFact))
      {
        continue;
      }

      String name = "this";
      Map<SmtVariable, SmtExpr> boundVariables = new HashMap<>();
      SmtVariable declaration = new SmtVariable(name, AbstractTranslator.atomSort, true);
      boundVariables.put(declaration, translator.signaturesMap.get(sigFact.getKey()).getVariable());
      SmtExpr member = AlloyUtils.getMemberExpression(boundVariables, 0);
      declaration.setConstraint(member);
      SmtEnv smtEnv = new SmtEnv();
      smtEnv.put(name, declaration.getVariable());

      SmtExpr bodyExpr = translator.exprTranslator.translateExpr(sigFact.getValue(), smtEnv);

      SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(member, bodyExpr);
      SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, new ArrayList<>(boundVariables.keySet()));
      Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(sigFact.getValue().pos),
          "Signature fact '" + sigFact.getValue().toString() + "' for sig " + sigFact.getKey(), forAll);
      translator.smtScript.addAssertion(assertion);
    }
  }

  private void translateTotalOrder(Sig ordSig, ExprList exprList, SmtEnv smtEnv)
  {
    if (exprList.args.size() != 3)
    {
      throw new UnsupportedOperationException();
    }

    Expr set = exprList.args.get(0);
    Expr first = exprList.args.get(1);

    // define a new uninterpreted one-to-one mapping from the signature to integers
    String label = ordSig.label;
    // convert ordA/Ord to ordA_
    String prefix = label.replaceFirst("/Ord", "/");
    String mappingName = prefix + "IntMapping";

    FunctionDeclaration mapping = defineInjectiveMapping(mappingName, AbstractTranslator.atomSort, translator.intSort);

    SmtExpr setSmtExpr = translator.exprTranslator.translateExpr(set, smtEnv);
    SmtExpr firstSmtExpr = translator.exprTranslator.translateExpr(first, smtEnv);

    // ordering/first
    SmtExpr firstSet = defineFirstElement(prefix, firstSmtExpr, mapping, setSmtExpr);

    // ordering/last
    FunctionDeclaration lastAtom = defineLastElement(prefix, mapping, setSmtExpr);

    // Next relation
    FunctionDeclaration ordNext = addOrdNext(prefix, setSmtExpr, mapping, ordSig, firstSet, lastAtom);

    // prev relation
    FunctionDeclaration ordPrev = addOrdPrev(prefix, ordNext);

    SmtVariable set1 = new SmtVariable("s1", translator.setOfUnaryAtomSort, false);
    SmtVariable set2 = new SmtVariable("s2", translator.setOfUnaryAtomSort, false);

    SmtVariable element1 = new SmtVariable("e1", AbstractTranslator.atomSort, false);
    SmtVariable element2 = new SmtVariable("e2", AbstractTranslator.atomSort, false);

    // ordering/prevs
    FunctionDefinition prevs = getPrevsNextsDefinition(prefix, set1, ordPrev, "prevs");
    translator.addFunction(prevs);

    // ordering/nexts
    FunctionDefinition nexts = getPrevsNextsDefinition(prefix, set1, ordNext, "nexts");
    translator.addFunction(nexts);

    // ordering/lt
    FunctionDefinition lt = getComparisonDefinition(prefix, "lt", mapping, set1, set2, element1, element2, SmtBinaryExpr.Op.LT);
    translator.addFunction(lt);

    // ordering/gt
    FunctionDefinition gt = getComparisonDefinition(prefix, "gt", mapping, set1, set2, element1, element2, SmtBinaryExpr.Op.GT);
    translator.addFunction(gt);

    // ordering/lte
    FunctionDefinition lte = getComparisonDefinition(prefix, "lte", mapping, set1, set2, element1, element2, SmtBinaryExpr.Op.LTE);
    translator.addFunction(lte);

    // ordering/gte
    FunctionDefinition gte = getComparisonDefinition(prefix, "gte", mapping, set1, set2, element1, element2, SmtBinaryExpr.Op.GTE);
    translator.addFunction(gte);

    //ordering/larger
    FunctionDefinition larger = getLargerSmallerDefinition(prefix, "larger", set1, set2, gt);
    translator.addFunction(larger);

    //ordering/smaller
    FunctionDefinition smaller = getLargerSmallerDefinition(prefix, "smaller", set1, set2, lt);
    translator.addFunction(smaller);

    //ordering/max
    FunctionDefinition max = getMaxMinDefinition(prefix, "max", set1, ordPrev);
    translator.addFunction(max);

    //ordering/min
    FunctionDefinition min = getMaxMinDefinition(prefix, "min", set1, ordNext);
    translator.addFunction(min);
  }

  private FunctionDeclaration defineInjectiveMapping(String mappingName, Sort inputSort, Sort outputSort)
  {
    FunctionDeclaration mapping = new FunctionDeclaration(mappingName, inputSort, outputSort, true);
    translator.addFunction(mapping);

    // the mapping is one-to-one(injective)
    // for all x, y (x != y and  implies f(x) != f(y))
    SmtVariable x = new SmtVariable("x", AbstractTranslator.atomSort, false);
    SmtVariable y = new SmtVariable("y", AbstractTranslator.atomSort, false);

    SmtExpr xEqualsY = SmtBinaryExpr.Op.EQ.make(x.getVariable(), y.getVariable());

    SmtExpr notXEqualsY = SmtUnaryExpr.Op.NOT.make(xEqualsY);

    SmtExpr mappingXEqualsMappingY = SmtBinaryExpr.Op.EQ.make(new SmtCallExpr(mapping, x.getVariable()), new SmtCallExpr(mapping, y.getVariable()));

    SmtExpr not = SmtUnaryExpr.Op.NOT.make(mappingXEqualsMappingY);

    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(notXEqualsY, not);

    SmtQtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, x, y);

    translator.smtScript.addAssertion(new Assertion("", mappingName + " is injective", forAll));

    return mapping;
  }

  private SmtExpr defineFirstElement(String prefix, SmtExpr firstSmtExpr, FunctionDeclaration mapping, SmtExpr setSmtExpr)
  {
    final String suffix = "first";
    FunctionDeclaration firstAtom = new FunctionDeclaration(prefix + "FirstAtom", AbstractTranslator.atomSort, true);
    FunctionDeclaration first = new FunctionDeclaration(prefix + suffix, AbstractTranslator.setOfUnaryAtomSort, true);

    SmtExpr firstSet = SmtUnaryExpr.Op.SINGLETON.make(
        new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, firstAtom.getVariable()));

    translator.smtScript.addFunction(firstAtom);
    translator.addFunction(first);

    // there is only one first element
    // ordering/first = (singleton (mktuple firstAtom))
    SmtExpr firstSingleton = SmtBinaryExpr.Op.EQ.make(first.getVariable(), firstSet);
    translator.smtScript.addAssertion(new Assertion("", prefix + suffix + " = (singleton (mktuple firstAtom))", firstSingleton));

    // ordering/first = ordering/Ord.First
    SmtExpr ordFirstSingleton = SmtBinaryExpr.Op.EQ.make(first.getVariable(), firstSmtExpr);
    translator.smtScript.addAssertion(new Assertion("", prefix + suffix + " = " + prefix + "Ord.First", ordFirstSingleton));

    // each element is greater than or equal to the first element
    SmtVariable x = new SmtVariable("x", AbstractTranslator.atomSort, false);
    SmtExpr member = SmtBinaryExpr.Op.MEMBER.make(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, x.getVariable()), setSmtExpr);
    SmtExpr gte = SmtBinaryExpr.Op.GTE.make(new SmtCallExpr(mapping, x.getVariable()), new SmtCallExpr(mapping, firstAtom.getVariable()));
    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(member, gte);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, x);
    translator.smtScript.addAssertion(new Assertion("",
        "each element is greater than or equal to the first element", forAll));

    return firstSet;
  }

  private FunctionDeclaration defineLastElement(String prefix, FunctionDeclaration mapping, SmtExpr setSmtExpr)
  {
    final String suffix = "last";
    FunctionDeclaration lastAtom = new FunctionDeclaration(prefix + "LastAtom", AbstractTranslator.atomSort, true);
    FunctionDeclaration last = new FunctionDeclaration(prefix + suffix, translator.setOfUnaryAtomSort, true);

    SmtExpr lastSet = SmtUnaryExpr.Op.SINGLETON.make(
        new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, lastAtom.getVariable()));

    translator.smtScript.addFunction(lastAtom);
    translator.addFunction(last);


    // last element is a member of the set
    SmtExpr lastMember = SmtBinaryExpr.Op.MEMBER.make(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, lastAtom.getVariable()), setSmtExpr);
    translator.smtScript.addAssertion(new Assertion("", "last element is a member", lastMember));

    // there is only one last element
    // ordering/last = (singleton (mktuple lastAtom))
    SmtExpr lastSingleton = SmtBinaryExpr.Op.EQ.make(last.getVariable(), lastSet);
    translator.smtScript.addAssertion(new Assertion("", prefix + suffix + " = (singleton (mktuple lastAtom))", lastSingleton));

    // each element is less than or equal to the last element
    SmtVariable x = new SmtVariable("x", AbstractTranslator.atomSort, false);
    SmtExpr xMember = SmtBinaryExpr.Op.MEMBER.make(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, x.getVariable()), setSmtExpr);
    SmtExpr lte = SmtBinaryExpr.Op.LTE.make(new SmtCallExpr(mapping, x.getVariable()), new SmtCallExpr(mapping, lastAtom.getVariable()));
    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(xMember, lte);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, x);
    translator.smtScript.addAssertion(new Assertion("",
        "each element is less than or equal to the last element", forAll));

    return lastAtom;
  }

  private FunctionDefinition getMaxMinDefinition(String prefix, String suffix, SmtVariable set, FunctionDeclaration declaration)
  {
    SmtExpr tClosure = SmtUnaryExpr.Op.TCLOSURE.make(declaration.getVariable());

    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(set.getVariable(), tClosure);

    SmtExpr difference = SmtBinaryExpr.Op.SETMINUS.make(set.getVariable(), join);

    return new FunctionDefinition(prefix + suffix, translator.setOfUnaryAtomSort,
        difference, true, set);
  }

  private FunctionDefinition getPrevsNextsDefinition(String prefix, SmtVariable set1, FunctionDeclaration ord, String suffix)
  {
    SmtUnaryExpr tClosure = SmtUnaryExpr.Op.TCLOSURE.make(ord.getVariable());
    SmtBinaryExpr join = SmtBinaryExpr.Op.JOIN.make(set1.getVariable(), tClosure);
    String name = prefix + suffix;
    FunctionDefinition definition = new FunctionDefinition(name, translator.setOfUnaryAtomSort, join, true, set1);
    return definition;
  }

  private FunctionDefinition getLargerSmallerDefinition(String prefix, String suffix, SmtVariable set1, SmtVariable set2, FunctionDefinition definition)
  {
    SmtCallExpr call = new SmtCallExpr(definition, set1.getVariable(), set2.getVariable());
    SmtIteExpr ite = new SmtIteExpr(call, set1.getVariable(),
        set2.getVariable());
    return new FunctionDefinition(prefix + suffix,
        translator.setOfUnaryAtomSort,
        ite, true,
        set1, set2
    );
  }

  private FunctionDeclaration addOrdNext(String prefix, SmtExpr setSmtExpr, FunctionDeclaration intMapping, Sig ordSig, SmtExpr firstSet, FunctionDeclaration lastAtom)
  {
    String nextMapping = prefix + "nextMapping";

    FunctionDeclaration mapping = new FunctionDeclaration(nextMapping, AbstractTranslator.atomSort, AbstractTranslator.atomSort, true);
    translator.addFunction(mapping);

    SmtVariable x = new SmtVariable("x", AbstractTranslator.atomSort, false);
    SmtVariable y = new SmtVariable("y", AbstractTranslator.atomSort, false);

    // for all x : x is a member implies intMapping(x) < intMapping (nextMapping(x)) and
    //                                                    x != lastAtom implies nextMapping(x) is a member

    SmtBinaryExpr xMember = SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(x), setSmtExpr);
    SmtBinaryExpr xLessThanNext = SmtBinaryExpr.Op.LT.make(new SmtCallExpr(intMapping, x.getVariable()), new SmtCallExpr(intMapping,
        new SmtCallExpr(mapping, x.getVariable())));

    SmtExpr notXEqualsLast = SmtUnaryExpr.Op.NOT.make(
        SmtBinaryExpr.Op.EQ.make(x.getVariable(), lastAtom.getVariable()));
    SmtExpr nextIsMember = SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(new SmtCallExpr(mapping, x.getVariable())), setSmtExpr);

    SmtExpr impliesNextIsMember = SmtBinaryExpr.Op.IMPLIES.make(notXEqualsLast, nextIsMember);

    SmtExpr xMemberconsequent = SmtMultiArityExpr.Op.AND.make(xLessThanNext, impliesNextIsMember);

    SmtExpr xMemberImplies = SmtBinaryExpr.Op.IMPLIES.make(xMember, xMemberconsequent);

    SmtExpr forAllX = SmtQtExpr.Op.FORALL.make(xMemberImplies, x);
    translator.smtScript.addAssertion(
        new Assertion("", "For all x : x is a member implies (intMapping(x) < intMapping (nextMapping(x)) and " +
            "(x != lastAtom implies nextMapping(x) is a member))", forAllX));

    // the next mapping is one-to-one (injective) members
    // for all x, y (x != y and x, y members) implies (nextMapping(x) != nextMapping(y)))
    SmtExpr xEqualsY = SmtBinaryExpr.Op.EQ.make(x.getVariable(), y.getVariable());
    SmtExpr notXEqualsY = SmtUnaryExpr.Op.NOT.make(xEqualsY);

    SmtExpr xyMembers = SmtMultiArityExpr.Op.AND.make(SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(x), setSmtExpr), SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(y), setSmtExpr));

    SmtExpr antecedent = SmtMultiArityExpr.Op.AND.make(notXEqualsY, xyMembers);

    SmtExpr mappingXEqualsMappingY = SmtBinaryExpr.Op.EQ.make(new SmtCallExpr(mapping, x.getVariable()), new SmtCallExpr(mapping, y.getVariable()));

    SmtExpr consequent = SmtUnaryExpr.Op.NOT.make(mappingXEqualsMappingY);

    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(antecedent, consequent);

    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, x, y);

    translator.smtScript.addAssertion(new Assertion("", nextMapping + " is injective for members", forAll));

    FunctionDeclaration ordNext = new FunctionDeclaration(prefix + "next", translator.setOfBinaryAtomSort, true);
    translator.addFunction(ordNext);

    // for all x, y (x,y) in the next relation iff x, y are members and nextMapping(x) = y
    SmtExpr xy = TranslatorUtils.getTuple(x, y);
    SmtExpr xyInNext = SmtBinaryExpr.Op.MEMBER.make(xy, ordNext.getVariable());

    SmtExpr xLessThanY = SmtBinaryExpr.Op.LT.make(new SmtCallExpr(intMapping, x.getVariable()), new SmtCallExpr(intMapping, y.getVariable()));

    SmtExpr nextXEqualsY = SmtBinaryExpr.Op.EQ.make(new SmtCallExpr(mapping, x.getVariable()), y.getVariable());

    SmtExpr and = SmtMultiArityExpr.Op.AND.make(xyMembers, nextXEqualsY);

    SmtBinaryExpr iff = SmtBinaryExpr.Op.EQ.make(xyInNext, and);

    SmtQtExpr forAllXY = SmtQtExpr.Op.FORALL.make(iff, x, y);
    translator.smtScript.addAssertion(new Assertion("", prefix + "next", forAllXY));

    SmtExpr ordSigSmtExpr = translator.signaturesMap.get(ordSig).getVariable();

    Sig.Field nextField = StreamSupport
        .stream(ordSig.getFields().spliterator(), false)
        .filter(field -> field.label.contains("Next"))
        .findFirst().get();

    SmtExpr nextFieldSmtExpr = translator.fieldsMap.get(nextField).getVariable();

    SmtExpr join = SmtBinaryExpr.Op.JOIN.make(ordSigSmtExpr, nextFieldSmtExpr);

    SmtExpr equality = SmtBinaryExpr.Op.EQ.make(ordNext.getVariable(), join);

    // next = ordSig.Next
    translator.smtScript.addAssertion(
        new Assertion("", ordNext.getName() + " = " + ordSig.label + "." + nextField.label, equality));

    // either (next is an empty set and the ordered set is a singleton) or next is nonempty
    SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(translator.setOfBinaryAtomSort);
    SmtExpr nextIsEmpty = SmtBinaryExpr.Op.EQ.make(ordNext.getVariable(), emptySet);
    SmtExpr setSingleton = SmtBinaryExpr.Op.EQ.make(setSmtExpr, firstSet);
    SmtExpr nextIsNonempty = SmtUnaryExpr.Op.NOT.make(nextIsEmpty);
    SmtExpr or = SmtMultiArityExpr.Op.OR.make(SmtMultiArityExpr.Op.AND.make(nextIsEmpty, setSingleton), nextIsNonempty);

    // either (next is an empty set and the ordered set is a singleton) or next is nonempty
    translator.smtScript.addAssertion(
        new Assertion("", "either (next is an empty set and the ordered set is a singleton) or next is nonempty", or));
    return ordNext;
  }

  private FunctionDeclaration addOrdPrev(String prefix, FunctionDeclaration ordNext)
  {
    FunctionDeclaration ordPrev = new FunctionDeclaration(prefix + "prev", translator.setOfBinaryAtomSort, true);

    SmtUnaryExpr transpose = SmtUnaryExpr.Op.TRANSPOSE.make(ordNext.getVariable());

    SmtBinaryExpr equality = SmtBinaryExpr.Op.EQ.make(ordPrev.getVariable(), transpose);

    translator.addFunction(ordPrev);

    translator.smtScript.addAssertion(new Assertion("", prefix + "PrevAuxiliary", equality));

    return ordPrev;
  }

  private FunctionDefinition getComparisonDefinition(String prefix, String suffix, FunctionDeclaration mapping, SmtVariable set1, SmtVariable set2, SmtVariable element1, SmtVariable element2, SmtBinaryExpr.Op operator)
  {
    SmtQtExpr ltExpression =
        SmtQtExpr.Op.FORALL.make(
            SmtBinaryExpr.Op.IMPLIES.make(SmtMultiArityExpr.Op.AND.make(SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(element1), set1.getVariable()), SmtBinaryExpr.Op.MEMBER.make(TranslatorUtils.getTuple(element2), set2.getVariable())), operator.make(new SmtCallExpr(mapping, element1.getVariable()), new SmtCallExpr(mapping, element1.getVariable()))),
            element1, element2
                                );

    return new FunctionDefinition(prefix + suffix,
        BoolSort.getInstance(),
        ltExpression, true,
        set1, set2
    );
  }
}
