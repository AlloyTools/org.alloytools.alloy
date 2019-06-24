/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
            if(sig instanceof Sig.PrimSig)
            {
                Sig.PrimSig primSig = (Sig.PrimSig) sig;

                if (primSig.isAbstract != null)
                {
                    SafeList<Sig.PrimSig> children = primSig.children();
                    if (children.size() > 0)
                    {
                        Expression left = translator.signaturesMap.get(sig).getVariable();
                        Expression union = translator.signaturesMap.get(children.get(0)).getVariable();

                        for (int i = 1; i < children.size(); i++)
                        {
                            Expression expression = translator.signaturesMap.get(children.get(i)).getVariable();
                            union = BinaryExpression.Op.UNION.make(union, expression);
                        }

                        BinaryExpression equality = BinaryExpression.Op.EQ.make(left, union);
                        Assertion isAbstract = new Assertion("abstract " + primSig.toString(), equality);
                        translator.smtProgram.addAssertion(isAbstract);
                    }
                }
            }
        }

        if (translator.topLevelSigs.size() > 0)
        {
            // The union of all top-level sigs equals to the universe
            Expression unionTopSigExprs = translator.signaturesMap.get(translator.topLevelSigs.get(0)).getVariable();

            for (int i = 1; i < translator.topLevelSigs.size(); ++i)
            {
                unionTopSigExprs = BinaryExpression.Op.UNION.make(unionTopSigExprs, translator.signaturesMap.get(translator.topLevelSigs.get(i)).getVariable());
            }
            translator.smtProgram.addAssertion(new Assertion(BinaryExpression.Op.EQ.make(unionTopSigExprs, translator.atomUniverse.getVariable())));

            // Top-level sigs are mutually disjoin
            if (translator.topLevelSigs.size() > 1)
            {
                for (int i = 0; i < translator.topLevelSigs.size() - 1; ++i)
                {
                    Expression fstSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(i)).getVariable();

                    for (int j = i + 1; j < translator.topLevelSigs.size(); ++j)
                    {
                        Expression sndSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(j)).getVariable();
                        translator.smtProgram.addAssertion(new Assertion(BinaryExpression.Op.EQ.make(BinaryExpression.Op.INTERSECTION.make(fstSigExpr, sndSigExpr), translator.atomNone.getVariable())));
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
            Expression left = translator.signaturesMap.get(signature).getVariable();

            for (int j = i + 1; j < signatures.size(); j++)
            {
                Expression right = translator.signaturesMap.get(signatures.get(j)).getVariable();
                BinaryExpression disjoint = BinaryExpression.Op.INTERSECTION.make(left, right);
                BinaryExpression equality = BinaryExpression.Op.EQ.make(disjoint, translator.atomNone.getVariable());

                translator.smtProgram.addAssertion(new Assertion("Disjoint signatures", equality));
            }
            // recursively add disjoint constraints to children
            if(signature instanceof Sig.PrimSig)
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
                FunctionDeclaration functionDeclaration = declareUnaryIntFunction(sig.toString());
                translator.signaturesMap.put(sig, functionDeclaration);
            }
            else
            {
                FunctionDeclaration functionDeclaration = declareUnaryAtomFunction(sig.toString());
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
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        if (isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.uninterpretedInt);
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);
        }
        expr = AlloyUtils.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getVariable()));
        translator.smtProgram.addConstantDeclaration(constDecl);

        BinaryExpression subset = BinaryExpression.Op.EQ.make(signature.getVariable(), expr);
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureLoneMultiplicity(Sig sig)
    {
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        if (isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.uninterpretedInt);
            expr = AlloyUtils.mkSingletonOutOfTuple(new FunctionCallExpression(translator.uninterpretedIntValue, constDecl.getVariable()));
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);
            expr = AlloyUtils.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getVariable()));
        }
        translator.smtProgram.addConstantDeclaration(constDecl);

        BinaryExpression subset = BinaryExpression.Op.SUBSET.make(signature.getVariable(), expr);
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureSomeMultiplicity(Sig sig)
    {
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        if (isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.uninterpretedInt);
            expr = AlloyUtils.mkSingletonOutOfTuple(new FunctionCallExpression(translator.uninterpretedIntValue, constDecl.getVariable()));
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);
            expr = AlloyUtils.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getVariable()));
        }
        translator.smtProgram.addConstantDeclaration(constDecl);

        BinaryExpression subset = BinaryExpression.Op.SUBSET.make(expr, signature.getVariable());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }


    private void translateSigSubsetParent(Sig sig, FunctionDeclaration functionDeclaration)
    {
        if (sig instanceof Sig.PrimSig)
        {
            Sig parent = ((Sig.PrimSig) sig).parent;
            FunctionDeclaration parentDeclaration = translator.signaturesMap.get(parent);
            BinaryExpression subsetExpression = BinaryExpression.Op.SUBSET.make(functionDeclaration.getVariable(), parentDeclaration.getVariable());
            translator.smtProgram.addAssertion(new Assertion(subsetExpression));
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
                    BinaryExpression subset = BinaryExpression.Op.SUBSET.make(functionDeclaration.getVariable(), parentDeclaration.getVariable());
                    translator.smtProgram.addAssertion(new Assertion(subset));
                }
            }
            else
            {
                Expression left = translator.signaturesMap.get(parents.get(0)).getVariable();
                Expression right = translator.signaturesMap.get(parents.get(1)).getVariable();
                BinaryExpression union = BinaryExpression.Op.UNION.make(left, right);

                for (int i = 2; i < parents.size(); i++)
                {
                    Expression expression = translator.signaturesMap.get(parents.get(i)).getVariable();
                    union = BinaryExpression.Op.UNION.make(union, expression);
                }

                BinaryExpression subset = BinaryExpression.Op.SUBSET.make(functionDeclaration.getVariable(), union);
                translator.smtProgram.addAssertion(new Assertion(subset));
            }
        }
    }

    private void declareIntSig()
    {
        translator.signaturesMap.put(Sig.SIGINT, translator.intUniv);
        BinaryExpression eqExpr = BinaryExpression.Op.EQ.make(translator.intUnivExpr, translator.intUniv.getVariable());
        translator.smtProgram.addFunction(translator.intUniv);
        translator.smtProgram.addAssertion(new Assertion(eqExpr));
    }


    private FunctionDeclaration declareUnaryAtomFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if (varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryAtomSort);
            translator.smtProgram.addFunction(declaration);
        }
        return declaration;
    }

    private FunctionDeclaration declareUnaryIntFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if (varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUninterpretedIntTuple);
            translator.smtProgram.addFunction(declaration);
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
            Environment environment = new Environment();
            Expr expr = sigFact.getValue();

            // handle total order operator differently
            if (expr instanceof ExprUnary &&
                    ((ExprUnary) expr).sub instanceof ExprList &&
                    ((ExprList) ((ExprUnary) expr).sub).op == ExprList.Op.TOTALORDER)
            {
                translateTotalOrder(sigFact.getKey(), ((ExprList) ((ExprUnary) expr).sub), environment);
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
            Map<VariableDeclaration, Expression> boundVariables = new HashMap<>();
            VariableDeclaration declaration = new VariableDeclaration(name, translator.atomSort, null);
            boundVariables.put(declaration, translator.signaturesMap.get(sigFact.getKey()).getVariable());
            Expression member = AlloyUtils.getMemberExpression(boundVariables, 0);
            declaration.setConstraint(member);
            Environment environment = new Environment();
            environment.put(name, declaration.getVariable());

            Expression bodyExpr = translator.exprTranslator.translateExpr(sigFact.getValue(), environment);

            translator.smtProgram.addAssertion(new Assertion("Fact for sig: " + sigFact.getKey(), QuantifiedExpression.Op.FORALL.make(BinaryExpression.Op.IMPLIES.make(member, bodyExpr), new ArrayList<>(boundVariables.keySet()))));
        }
    }

    private void translateTotalOrder(Sig ordSig, ExprList exprList, Environment environment)
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

        FunctionDeclaration mapping = defineInjectiveMapping(mappingName, translator.atomSort, translator.intSort);

        Expression setExpression = translator.exprTranslator.translateExpr(set, environment);
        Expression firstExpression = translator.exprTranslator.translateExpr(first, environment);

        // ordering/first
        Expression firstSet = defineFirstElement(prefix, firstExpression, mapping, setExpression);

        // ordering/last
        ConstantDeclaration lastAtom = defineLastElement(prefix, mapping, setExpression);

        // Next relation
        FunctionDeclaration ordNext = addOrdNext(prefix, setExpression, mapping, ordSig, firstSet, lastAtom);

        // prev relation
        FunctionDeclaration ordPrev = addOrdPrev(prefix, ordNext);

        VariableDeclaration set1 = new VariableDeclaration("s1", translator.setOfUnaryAtomSort, null);
        VariableDeclaration set2 = new VariableDeclaration("s2", translator.setOfUnaryAtomSort, null);

        VariableDeclaration element1 = new VariableDeclaration("e1", translator.atomSort, null);
        VariableDeclaration element2 = new VariableDeclaration("e2", translator.atomSort, null);

        // ordering/prevs
        FunctionDefinition prevs = getPrevsNextsDefinition(prefix, set1, ordPrev, "prevs");
        translator.addFunction(prevs);

        // ordering/nexts
        FunctionDefinition nexts = getPrevsNextsDefinition(prefix, set1, ordNext, "nexts");
        translator.addFunction(nexts);

        // ordering/lt
        FunctionDefinition lt = getComparisonDefinition(prefix, "lt", mapping, set1, set2, element1, element2, BinaryExpression.Op.LT);
        translator.addFunction(lt);

        // ordering/gt
        FunctionDefinition gt = getComparisonDefinition(prefix, "gt", mapping, set1, set2, element1, element2, BinaryExpression.Op.GT);
        translator.addFunction(gt);

        // ordering/lte
        FunctionDefinition lte = getComparisonDefinition(prefix, "lte", mapping, set1, set2, element1, element2, BinaryExpression.Op.LTE);
        translator.addFunction(lte);

        // ordering/gte
        FunctionDefinition gte = getComparisonDefinition(prefix, "gte", mapping, set1, set2, element1, element2, BinaryExpression.Op.GTE);
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
        FunctionDeclaration mapping = new FunctionDeclaration(mappingName, inputSort, outputSort);
        translator.addFunction(mapping);

        // the mapping is one-to-one(injective)
        // for all x, y (x != y and  implies f(x) != f(y))
        VariableDeclaration x = new VariableDeclaration("__x__", translator.atomSort, null);
        VariableDeclaration y = new VariableDeclaration("__y__", translator.atomSort, null);

        Expression xEqualsY = BinaryExpression.Op.EQ.make(x.getVariable(), y.getVariable());

        Expression notXEqualsY = UnaryExpression.Op.NOT.make(xEqualsY);

        Expression mappingXEqualsMappingY = BinaryExpression.Op.EQ.make(new FunctionCallExpression(mapping, x.getVariable()), new FunctionCallExpression(mapping, y.getVariable()));

        Expression not = UnaryExpression.Op.NOT.make(mappingXEqualsMappingY);

        Expression implies = BinaryExpression.Op.IMPLIES.make(notXEqualsY, not);

        QuantifiedExpression forAll = QuantifiedExpression.Op.FORALL.make(implies, x, y);

        translator.smtProgram.addAssertion(new Assertion(mappingName + " is injective", forAll));

        return mapping;
    }

    private Expression defineFirstElement(String prefix, Expression firstExpression, FunctionDeclaration mapping, Expression setExpression)
    {
        final String suffix = "first";
        ConstantDeclaration firstAtom = new ConstantDeclaration(prefix + "FirstAtom", translator.atomSort);
        FunctionDeclaration first = new FunctionDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression firstSet = UnaryExpression.Op.SINGLETON.make(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getVariable()));

        translator.smtProgram.addConstantDeclaration(firstAtom);
        translator.addFunction(first);

        // there is only one first element
        // ordering/first = (singleton (mktuple firstAtom))
        Expression firstSingleton = BinaryExpression.Op.EQ.make(first.getVariable(), firstSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = (singleton (mktuple firstAtom))", firstSingleton));

        // ordering/first = ordering/Ord.First
        Expression ordFirstSingleton = BinaryExpression.Op.EQ.make(first.getVariable(), firstExpression);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = " + prefix + "Ord.First", ordFirstSingleton));

        // each element is greater than or equal to the first element
        VariableDeclaration x = new VariableDeclaration("__x__", translator.atomSort, null);
        Expression member = BinaryExpression.Op.MEMBER.make(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable()), setExpression);
        Expression gte = BinaryExpression.Op.GTE.make(new FunctionCallExpression(mapping, x.getVariable()), new FunctionCallExpression(mapping, firstAtom.getVariable()));
        Expression implies = BinaryExpression.Op.IMPLIES.make(member, gte);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is greater than or equal to the first element", forAll));

        return firstSet;
    }

    private ConstantDeclaration defineLastElement(String prefix, FunctionDeclaration mapping, Expression setExpression)
    {
        final String suffix = "last";
        ConstantDeclaration lastAtom = new ConstantDeclaration(prefix + "LastAtom", translator.atomSort);
        FunctionDeclaration last = new FunctionDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression lastSet = UnaryExpression.Op.SINGLETON.make(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getVariable()));

        translator.smtProgram.addConstantDeclaration(lastAtom);
        translator.addFunction(last);


        // last element is a member of the set
        Expression lastMember = BinaryExpression.Op.MEMBER.make(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getVariable()), setExpression);
        translator.smtProgram.addAssertion(new Assertion("last element is a member", lastMember));

        // there is only one last element
        // ordering/last = (singleton (mktuple lastAtom))
        Expression lastSingleton = BinaryExpression.Op.EQ.make(last.getVariable(), lastSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = (singleton (mktuple lastAtom))", lastSingleton));

        // each element is less than or equal to the last element
        VariableDeclaration x = new VariableDeclaration("__x__", translator.atomSort, null);
        Expression xMember = BinaryExpression.Op.MEMBER.make(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable()), setExpression);
        Expression lte = BinaryExpression.Op.LTE.make(new FunctionCallExpression(mapping, x.getVariable()), new FunctionCallExpression(mapping, lastAtom.getVariable()));
        Expression implies = BinaryExpression.Op.IMPLIES.make(xMember, lte);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is less than or equal to the last element", forAll));

        return lastAtom;
    }

    private FunctionDefinition getMaxMinDefinition(String prefix, String suffix, VariableDeclaration set, FunctionDeclaration declaration)
    {
        Expression tClosure = UnaryExpression.Op.TCLOSURE.make(declaration.getVariable());

        Expression join = BinaryExpression.Op.JOIN.make(set.getVariable(), tClosure);

        Expression difference = BinaryExpression.Op.SETMINUS.make(set.getVariable(), join);

        return new FunctionDefinition(prefix + suffix, translator.setOfUnaryAtomSort,
                difference, set);
    }

    private FunctionDefinition getPrevsNextsDefinition(String prefix, VariableDeclaration set1, FunctionDeclaration ord, String suffix)
    {
        UnaryExpression tClosure = UnaryExpression.Op.TCLOSURE.make(ord.getVariable());
        BinaryExpression join = BinaryExpression.Op.JOIN.make(set1.getVariable(), tClosure);
        String name = prefix + suffix;
        FunctionDefinition definition = new FunctionDefinition(name, translator.setOfUnaryAtomSort, join, set1);
        return definition;
    }

    private FunctionDefinition getLargerSmallerDefinition(String prefix, String suffix, VariableDeclaration set1, VariableDeclaration set2, FunctionDefinition definition)
    {
        FunctionCallExpression call = new FunctionCallExpression(definition, set1.getVariable(), set2.getVariable());
        ITEExpression ite = new ITEExpression(call, set1.getVariable(),
                set2.getVariable());
        return new FunctionDefinition(prefix + suffix,
                translator.setOfUnaryAtomSort,
                ite,
                set1, set2
        );
    }

    private FunctionDeclaration addOrdNext(String prefix, Expression setExpression, FunctionDeclaration intMapping, Sig ordSig, Expression firstSet, ConstantDeclaration lastAtom)
    {
        String nextMapping = prefix + "nextMapping";

        FunctionDeclaration mapping = new FunctionDeclaration(nextMapping, translator.atomSort, translator.atomSort);
        translator.addFunction(mapping);

        VariableDeclaration x = new VariableDeclaration("__x__", translator.atomSort, null);
        VariableDeclaration y = new VariableDeclaration("__y__", translator.atomSort, null);

        // for all x : x is a member implies intMapping(x) < intMapping (nextMapping(x)) and
        //                                                    x != lastAtom implies nextMapping(x) is a member

        BinaryExpression xMember = BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(x), setExpression);
        BinaryExpression xLessThanNext = BinaryExpression.Op.LT.make(new FunctionCallExpression(intMapping, x.getVariable()), new FunctionCallExpression(intMapping,
                        new FunctionCallExpression(mapping, x.getVariable())));

        Expression notXEqualsLast = UnaryExpression.Op.NOT.make(
                BinaryExpression.Op.EQ.make(x.getVariable(), lastAtom.getVariable()));
        Expression nextIsMember = BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(new FunctionCallExpression(mapping, x.getVariable())), setExpression);

        Expression impliesNextIsMember = BinaryExpression.Op.IMPLIES.make(notXEqualsLast, nextIsMember);

        Expression xMemberconsequent = BinaryExpression.Op.AND.make(xLessThanNext, impliesNextIsMember);

        Expression xMemberImplies = BinaryExpression.Op.IMPLIES.make(xMember, xMemberconsequent);

        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xMemberImplies, x);
        translator.smtProgram.addAssertion(
                new Assertion("For all x : x is a member implies (intMapping(x) < intMapping (nextMapping(x)) and " +
                        "(x != lastAtom implies nextMapping(x) is a member))", forAllX));

        // the next mapping is one-to-one (injective) members
        // for all x, y (x != y and x, y members) implies (nextMapping(x) != nextMapping(y)))
        Expression xEqualsY = BinaryExpression.Op.EQ.make(x.getVariable(), y.getVariable());
        Expression notXEqualsY = UnaryExpression.Op.NOT.make(xEqualsY);

        Expression xyMembers = BinaryExpression.Op.AND.make(BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(x), setExpression), BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(y), setExpression));

        Expression antecedent = BinaryExpression.Op.AND.make(notXEqualsY, xyMembers);

        Expression mappingXEqualsMappingY = BinaryExpression.Op.EQ.make(new FunctionCallExpression(mapping, x.getVariable()), new FunctionCallExpression(mapping, y.getVariable()));

        Expression consequent = UnaryExpression.Op.NOT.make(mappingXEqualsMappingY);

        Expression implies = BinaryExpression.Op.IMPLIES.make(antecedent, consequent);

        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, x, y);

        translator.smtProgram.addAssertion(new Assertion(nextMapping + " is injective for members", forAll));

        FunctionDeclaration ordNext = new FunctionDeclaration(prefix + "next", translator.setOfBinaryAtomSort);
        translator.addFunction(ordNext);

        // for all x, y (x,y) in the next relation iff x, y are members and nextMapping(x) = y
        Expression xy = TranslatorUtils.getTuple(x, y);
        Expression xyInNext = BinaryExpression.Op.MEMBER.make(xy, ordNext.getVariable());

        Expression xLessThanY = BinaryExpression.Op.LT.make(new FunctionCallExpression(intMapping, x.getVariable()), new FunctionCallExpression(intMapping, y.getVariable()));

        Expression nextXEqualsY = BinaryExpression.Op.EQ.make(new FunctionCallExpression(mapping, x.getVariable()), y.getVariable());

        Expression and = BinaryExpression.Op.AND.make(xyMembers, nextXEqualsY);

        BinaryExpression iff = BinaryExpression.Op.EQ.make(xyInNext, and);

        QuantifiedExpression forAllXY = QuantifiedExpression.Op.FORALL.make(iff, x, y);
        translator.smtProgram.addAssertion(new Assertion(prefix + "next", forAllXY));

        Expression ordSigExpression = translator.signaturesMap.get(ordSig).getVariable();

        Sig.Field nextField = StreamSupport
                .stream(ordSig.getFields().spliterator(), false)
                .filter(field -> field.label.contains("Next"))
                .findFirst().get();

        Expression nextFieldExpression = translator.fieldsMap.get(nextField).getVariable();

        Expression join = BinaryExpression.Op.JOIN.make(ordSigExpression, nextFieldExpression);

        Expression equality = BinaryExpression.Op.EQ.make(ordNext.getVariable(), join);

        // next = ordSig.Next
        translator.smtProgram.addAssertion(
                new Assertion(ordNext.getName() + " = " + ordSig.label + "." + nextField.label, equality));

        // either (next is an empty set and the ordered set is a singleton) or next is nonempty
        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(translator.setOfBinaryAtomSort);
        Expression nextIsEmpty = BinaryExpression.Op.EQ.make(ordNext.getVariable(), emptySet);
        Expression setSingleton = BinaryExpression.Op.EQ.make(setExpression, firstSet);
        Expression nextIsNonempty = UnaryExpression.Op.NOT.make(nextIsEmpty);
        Expression or = BinaryExpression.Op.OR.make(BinaryExpression.Op.AND.make(nextIsEmpty, setSingleton), nextIsNonempty);

        // either (next is an empty set and the ordered set is a singleton) or next is nonempty
        translator.smtProgram.addAssertion(
                new Assertion("either (next is an empty set and the ordered set is a singleton) or next is nonempty", or));
        return ordNext;
    }

    private FunctionDeclaration addOrdPrev(String prefix, FunctionDeclaration ordNext)
    {
        FunctionDeclaration ordPrev = new FunctionDeclaration(prefix + "prev", translator.setOfBinaryAtomSort);

        UnaryExpression transpose = UnaryExpression.Op.TRANSPOSE.make(ordNext.getVariable());

        BinaryExpression equality = BinaryExpression.Op.EQ.make(ordPrev.getVariable(), transpose);

        translator.addFunction(ordPrev);

        translator.smtProgram.addAssertion(new Assertion(prefix + "PrevAuxiliary", equality));

        return ordPrev;
    }

    private FunctionDefinition getComparisonDefinition(String prefix, String suffix, FunctionDeclaration mapping, VariableDeclaration set1, VariableDeclaration set2, VariableDeclaration element1, VariableDeclaration element2, BinaryExpression.Op operator)
    {
        QuantifiedExpression ltExpression =
                        QuantifiedExpression.Op.FORALL.make(
                                BinaryExpression.Op.IMPLIES.make(BinaryExpression.Op.AND.make(BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(element1), set1.getVariable()), BinaryExpression.Op.MEMBER.make(TranslatorUtils.getTuple(element2), set2.getVariable())), operator.make(new FunctionCallExpression(mapping, element1.getVariable()), new FunctionCallExpression(mapping, element1.getVariable()))),
                                element1, element2
                        );

        return new FunctionDefinition(prefix + suffix,
                BoolSort.getInstance(),
                ltExpression,
                set1, set2
        );
    }
}
