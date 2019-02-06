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
import edu.uiowa.alloy2smt.smtAst.*;

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
        this.translator         = translator;
        this.fieldTranslator    = new FieldTranslator(translator);
    }

    private void translateSignatureHierarchies()
    {
        for (Sig sig: translator.topLevelSigs)
        {            
            Sig.PrimSig primSig = (Sig.PrimSig) sig;
            translateDisjointSignatures(primSig.children().makeCopy().stream().map(p -> (Sig) p).collect(Collectors.toList()));
            
            if(primSig.isAbstract != null)
            {
                SafeList<Sig.PrimSig> children = primSig.children();
                if(children.size() == 1)
                {
                    Expression          left        = translator.signaturesMap.get(sig).getConstantExpr();
                    Expression          right       = translator.signaturesMap.get(children.get(0)).getConstantExpr();
                    BinaryExpression equality       = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
                    translator.smtProgram.addAssertion(new Assertion(equality));
                }
                else if(children.size() > 1)
                {

                    Expression          left        = translator.signaturesMap.get(children.get(0)).getConstantExpr();
                    Expression          right       = translator.signaturesMap.get(children.get(1)).getConstantExpr();
                    BinaryExpression    union       = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                    for(int i = 2; i < children.size(); i++)
                    {
                        Expression      expression  = translator.signaturesMap.get(children.get(i)).getConstantExpr();
                        union                       = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                    }

                    Expression          leftExpr    = translator.signaturesMap.get(sig).getConstantExpr();
                    BinaryExpression    equality    = new BinaryExpression(leftExpr, BinaryExpression.Op.EQ, union);
                    translator.smtProgram.addAssertion(new Assertion(equality));
                }
            }
        }
                
        if(translator.topLevelSigs.size() > 0)
        {
            // The union of all top-level sigs equals to the universe
            Expression unionTopSigExprs = translator.signaturesMap.get(translator.topLevelSigs.get(0)).getConstantExpr();
            
            for(int i = 1; i < translator.topLevelSigs.size(); ++i)
            {
                unionTopSigExprs = new BinaryExpression(unionTopSigExprs, BinaryExpression.Op.UNION, translator.signaturesMap.get(translator.topLevelSigs.get(i)).getConstantExpr());
            }
            translator.smtProgram.addAssertion(new Assertion(new BinaryExpression(unionTopSigExprs, BinaryExpression.Op.EQ, translator.atomUniv.getConstantExpr())));
            
            // Top-level sigs are mutually disjoin
            if(translator.topLevelSigs.size() > 1)
            {
                for(int i = 0; i < translator.topLevelSigs.size()-1; ++i)
                {
                    Expression fstSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(i)).getConstantExpr();
                    
                    for(int j = i+1; j < translator.topLevelSigs.size();++j)
                    {
                        Expression sndSigExpr = translator.signaturesMap.get(translator.topLevelSigs.get(j)).getConstantExpr();
                        translator.smtProgram.addAssertion(new Assertion(new BinaryExpression(new BinaryExpression(fstSigExpr, BinaryExpression.Op.INTERSECTION, sndSigExpr), BinaryExpression.Op.EQ, translator.atomNone.getConstantExpr())));
                    }
                }
            }
            
        }
    }

    private void translateDisjointSignatures(List<Sig> signatures)
    {
        for (int i = 0; i < signatures.size(); i++)
        {
            Expression      left    = translator.signaturesMap.get(signatures.get(i)).getConstantExpr();

            for (int j = i + 1 ; j < signatures.size(); j++)
            {
                Expression          right       = translator.signaturesMap.get(signatures.get(j)).getConstantExpr();
                BinaryExpression    disjoint    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);
                BinaryExpression    equality    = new BinaryExpression(disjoint, BinaryExpression.Op.EQ, translator.atomNone.getConstantExpr());

                translator.smtProgram.addAssertion(new Assertion(equality));
            }
        }
    }

    private void collectReachableSigs()
    {
        for(Sig sig : translator.alloyModel.getAllReachableSigs())
        {
            if(sig.builtin)
            {
                continue;
            }
            if(sig.isTopLevel())
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
                FunctionDeclaration functionDeclaration = declareUnaryIntFunction(TranslatorUtils.sanitizeName(sig.toString()));
                translator.signaturesMap.put(sig, functionDeclaration);
            }
            else
            {
                FunctionDeclaration functionDeclaration = declareUnaryAtomFunction(TranslatorUtils.sanitizeName(sig.toString()));
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

            // translateExpr signature fields
            for (Sig.Field field : sig.getFields())
            {
                this.fieldTranslator.fields.add(field);
            }
            for (Expr expr : sig.getFacts())
            {
                translator.sigFacts.put(sig, expr);
            }
        }
        //ToDo: important review the logic for cardinality in the case of
        // top level signatures and the case of subset signatures.
        //translateDisjointSignatures(translator.topLevelSigs);
    }

    private void translateSignatureOneMultiplicity(Sig sig)
    {        
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();        
        FunctionDeclaration signature = translator.signaturesMap.get(sig);                        
        
        if(isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.unaryIntTup);
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup, constDecl.getConstantExpr()));
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);       
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getConstantExpr()));
        }
        translator.smtProgram.addConstantDeclaration(constDecl);
        
        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.EQ, expr);
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureLoneMultiplicity(Sig sig)
    {
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();        
        FunctionDeclaration signature = translator.signaturesMap.get(sig);          
        
        if(isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.unaryIntTup);            
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup, constDecl.getConstantExpr()));
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);       
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getConstantExpr()));
        }
        translator.smtProgram.addConstantDeclaration(constDecl);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.SUBSET, expr);
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureSomeMultiplicity(Sig sig)
    {
        Expression expr;
        ConstantDeclaration constDecl;
        Boolean isInt = sig.type().is_int();
        String name = TranslatorUtils.getNewName();        
        FunctionDeclaration signature = translator.signaturesMap.get(sig);  
        
        if(isInt)
        {
            constDecl = new ConstantDeclaration(name, translator.unaryIntTup);            
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup, constDecl.getConstantExpr()));
        }
        else
        {
            constDecl = new ConstantDeclaration(name, translator.atomSort);       
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constDecl.getConstantExpr()));
        }
        translator.smtProgram.addConstantDeclaration(constDecl);

        BinaryExpression subset   = new BinaryExpression(expr, BinaryExpression.Op.SUBSET, signature.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }



    private void translateSigSubsetParent(Sig sig, FunctionDeclaration functionDeclaration)
    {
        if(sig instanceof Sig.PrimSig)
        {
            Sig                 parent              = ((Sig.PrimSig) sig).parent;
            FunctionDeclaration parentDeclaration   = translator.signaturesMap.get(parent);
            BinaryExpression    subsetExpression    = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
            translator.smtProgram.addAssertion(new Assertion(subsetExpression));
        }
        else
        {
            List<Sig> parents   = ((Sig.SubsetSig) sig).parents;
            
            if(parents.size() == 1)
            {
                Sig parentSig = parents.get(0);
                
                // We consider parentSig as int
//                if(parentSig == Sig.SIGINT && !translator.signaturesMap.containsKey(parentSig))
//                {
//                    declareIntSig();
//                }
                if(parentSig != Sig.SIGINT)
                {
                    FunctionDeclaration parentDeclaration   = translator.signaturesMap.get(parentSig);
                    BinaryExpression    subset              = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
                    translator.smtProgram.addAssertion(new Assertion(subset));                                         
                }
            }
            else
            {
                Expression          left    = translator.signaturesMap.get(parents.get(0)).getConstantExpr();
                Expression          right   = translator.signaturesMap.get(parents.get(1)).getConstantExpr();
                BinaryExpression    union   = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                for (int i = 2; i < parents.size(); i++)
                {
                    Expression expression   = translator.signaturesMap.get(parents.get(i)).getConstantExpr();
                    union                   = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                }

                BinaryExpression subset     = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, union);
                translator.smtProgram.addAssertion(new Assertion(subset));
            }
        }
    }
    
    private void declareIntSig()
    {
        translator.signaturesMap.put(Sig.SIGINT, translator.intUniv);
        BinaryExpression    eqExpr  = new BinaryExpression(translator.intUnivExpr, BinaryExpression.Op.EQ, translator.intUniv.getConstantExpr());
        translator.smtProgram.addFunction(translator.intUniv);
        translator.smtProgram.addAssertion(new Assertion(eqExpr));           
    }


    private FunctionDeclaration declareUnaryAtomFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryAtomSort);
            translator.smtProgram.addFunction(declaration);
        }
        return declaration;
    }
    
    private FunctionDeclaration declareUnaryIntFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryIntSort);
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
            Map<String, Expression> variablesScope = new HashMap<>();
            Expr expr = sigFact.getValue();

            // handle total order operator differently
            if (expr instanceof ExprUnary &&
                    ((ExprUnary) expr).sub instanceof ExprList &&
                    ((ExprList) ((ExprUnary) expr).sub).op == ExprList.Op.TOTALORDER)
            {
                translateTotalOrder(sigFact.getKey(), ((ExprList) ((ExprUnary) expr).sub), variablesScope);
                this.translatedSigFacts.add(sigFact);
            }
        }
    }


    void translateSigFacts()
    {
        // Translate facts on signatures
        for(Map.Entry<Sig, Expr> sigFact : translator.sigFacts.entrySet())
        {
            // ignore already translated signature facts
            if(this.translatedSigFacts.contains(sigFact))
            {
                continue;
            }

            String bdVarName = "this";
            Map<VariableDeclaration, Expression> boundVariables = new HashMap<>();
            VariableDeclaration bdVar = new VariableDeclaration(bdVarName, translator.atomSort);
            boundVariables.put(bdVar, translator.signaturesMap.get(sigFact.getKey()).getConstantExpr());
            Expression member = translator.exprTranslator.getMemberExpression(boundVariables, 0);
            Map<String, Expression> variablesScope = new HashMap<>();

            variablesScope.put(bdVarName, new ConstantExpression(new FunctionDeclaration(bdVarName, translator.atomSort)));

            Expression bodyExpr = translator.exprTranslator.translateExpr(sigFact.getValue(), variablesScope);

            translator.smtProgram.addAssertion(new Assertion("Fact for sig: " + sigFact.getKey(), new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), new BinaryExpression(member, BinaryExpression.Op.IMPLIES, bodyExpr))));
        }
    }

    private void translateTotalOrder(Sig ordSig, ExprList exprList, Map<String, Expression> variablesScope)
    {
        if(exprList.args.size() != 3)
        {
            throw new UnsupportedOperationException();
        }

        Expr       set                  = exprList.args.get(0);
        Expr       first                = exprList.args.get(1);

        // define a new uninterpreted one-to-one mapping from the signature to integers
        String              label       = ordSig.label;
        // convert ordA/Ord to ordA_
        String              prefix      = label.replaceFirst("/Ord", "_");
        String              mappingName = TranslatorUtils.sanitizeName(prefix + "IntMapping");

        FunctionDeclaration mapping     = defineInjectiveMapping(mappingName, translator.atomSort, translator.intSort);

        Expression setExpression        = translator.exprTranslator.translateExpr(set, variablesScope);
        Expression firstExpression      = translator.exprTranslator.translateExpr(first, variablesScope);

        // ordering/first
        Expression firstSet             = defineFirstElement(prefix, firstExpression, mapping, setExpression);

        // ordering/last
        ConstantDeclaration lastAtom    = defineLastElement(prefix, mapping, setExpression);

        // Next relation
        FunctionDeclaration ordNext     =  addOrdNext(prefix,setExpression, mapping, ordSig, firstSet, lastAtom);

        // prev relation
        FunctionDeclaration ordPrev     = addOrdPrev(prefix, ordNext);

        VariableDeclaration set1   = new VariableDeclaration("s1", translator.setOfUnaryAtomSort);
        VariableDeclaration set2   = new VariableDeclaration("s2", translator.setOfUnaryAtomSort);

        VariableDeclaration element1 = new VariableDeclaration("e1", translator.atomSort);
        VariableDeclaration element2 = new VariableDeclaration("e2", translator.atomSort);

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
        FunctionDeclaration mapping     = new FunctionDeclaration(mappingName, inputSort, outputSort);
        translator.addFunction(mapping);

        // the mapping is one-to-one(injective)
        // for all x, y (x != y and  implies f(x) != f(y))
        VariableDeclaration x = new VariableDeclaration("_x", translator.atomSort);
        VariableDeclaration y = new VariableDeclaration("_y", translator.atomSort);

        Expression xEqualsY = new BinaryExpression(x.getConstantExpr(), BinaryExpression.Op.EQ, y.getConstantExpr());

        Expression notXEqualsY = new UnaryExpression(UnaryExpression.Op.NOT, xEqualsY);

        Expression mappingXEqualsMappingY = new BinaryExpression(
                new FunctionCallExpression(mapping, x.getConstantExpr()),
                BinaryExpression.Op.EQ,
                new FunctionCallExpression(mapping, y.getConstantExpr()));

        Expression not = new UnaryExpression(UnaryExpression.Op.NOT, mappingXEqualsMappingY);

        Expression implies = new BinaryExpression(notXEqualsY, BinaryExpression.Op.IMPLIES, not);

        QuantifiedExpression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, x, y);

        translator.smtProgram.addAssertion(new Assertion(mappingName + " is injective", forAll));

        return mapping;
    }

    private Expression defineFirstElement(String prefix, Expression firstExpression, FunctionDeclaration mapping, Expression setExpression)
    {
        final String suffix = "first";
        ConstantDeclaration firstAtom   = new ConstantDeclaration(prefix + "FirstAtom", translator.atomSort);
        FunctionDeclaration first       = new FunctionDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression          firstSet    = new UnaryExpression(UnaryExpression.Op.SINGLETON,
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getConstantExpr()));

        translator.smtProgram.addConstantDeclaration(firstAtom);
        translator.addFunction(first);

        // there is only one first element
        // ordering/first = (singleton (mktuple firstAtom))
        Expression firstSingleton       = new BinaryExpression(first.getConstantExpr(), BinaryExpression.Op.EQ, firstSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = (singleton (mktuple firstAtom))", firstSingleton));

        // ordering/first = ordering/Ord.First
        Expression ordFirstSingleton    = new BinaryExpression(first.getConstantExpr(), BinaryExpression.Op.EQ, firstExpression);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = " + prefix + "Ord.First", ordFirstSingleton));

        // each element is greater than or equal to the first element
        VariableDeclaration x = new VariableDeclaration("x", translator.atomSort);
        Expression member = new BinaryExpression(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr()),
                BinaryExpression.Op.MEMBER, setExpression);
        Expression gte = new BinaryExpression(
                new FunctionCallExpression(mapping, x.getConstantExpr()),
                BinaryExpression.Op.GTE,
                new FunctionCallExpression(mapping, firstAtom.getConstantExpr()));
        Expression implies = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, gte);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is greater than or equal to the first element", forAll));

        return firstSet;
    }

    private ConstantDeclaration defineLastElement(String prefix, FunctionDeclaration mapping, Expression setExpression)
    {
        final String suffix = "last";
        ConstantDeclaration lastAtom   = new ConstantDeclaration(prefix + "LastAtom", translator.atomSort);
        FunctionDeclaration last       = new FunctionDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression          lastSet    = new UnaryExpression(UnaryExpression.Op.SINGLETON,
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getConstantExpr()));

        translator.smtProgram.addConstantDeclaration(lastAtom);
        translator.addFunction(last);


        // last element is a member of the set
        Expression lastMember = new BinaryExpression(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getConstantExpr()),
                BinaryExpression.Op.MEMBER,
                setExpression);
        translator.smtProgram.addAssertion(new Assertion ("last element is a member", lastMember));

        // there is only one last element
        // ordering/last = (singleton (mktuple lastAtom))
        Expression lastSingleton       = new BinaryExpression(last.getConstantExpr(), BinaryExpression.Op.EQ, lastSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = (singleton (mktuple lastAtom))", lastSingleton));

        // each element is less than or equal to the last element
        VariableDeclaration x = new VariableDeclaration("x", translator.atomSort);
        Expression xMember = new BinaryExpression(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr()),
                BinaryExpression.Op.MEMBER, setExpression);
        Expression lte = new BinaryExpression(
                new FunctionCallExpression(mapping, x.getConstantExpr()),
                BinaryExpression.Op.LTE,
                new FunctionCallExpression(mapping, lastAtom.getConstantExpr()));
        Expression implies = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, lte);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is less than or equal to the last element", forAll));

        return lastAtom;
    }

    private FunctionDefinition getMaxMinDefinition(String prefix, String suffix, VariableDeclaration set, FunctionDeclaration declaration)
    {
        Expression tClosure     = new UnaryExpression(UnaryExpression.Op.TCLOSURE, declaration.getConstantExpr());

        Expression join         = new BinaryExpression(set.getConstantExpr(), BinaryExpression.Op.JOIN, tClosure);

        Expression difference   = new BinaryExpression(set.getConstantExpr(), BinaryExpression.Op.SETMINUS, join);

        return new FunctionDefinition(prefix + suffix, translator.setOfUnaryAtomSort,
                difference, set);
    }

    private FunctionDefinition getPrevsNextsDefinition(String prefix, VariableDeclaration set1, FunctionDeclaration ord, String suffix)
    {
        UnaryExpression tClosure = new UnaryExpression(UnaryExpression.Op.TCLOSURE, ord.getConstantExpr());
        BinaryExpression join = new BinaryExpression(set1.getConstantExpr(), BinaryExpression.Op.JOIN, tClosure);
        String name = prefix + suffix;
        FunctionDefinition definition = new FunctionDefinition(name, translator.setOfUnaryAtomSort, join, set1);
        return definition;
    }

    private FunctionDefinition getLargerSmallerDefinition(String prefix, String suffix, VariableDeclaration set1, VariableDeclaration set2, FunctionDefinition definition)
    {
        FunctionCallExpression call = new FunctionCallExpression(definition, set1.getConstantExpr(), set2.getConstantExpr());
        ITEExpression ite = new ITEExpression(call, set1.getConstantExpr(),
                set2.getConstantExpr());
        return new FunctionDefinition(prefix + suffix,
                translator.setOfUnaryAtomSort,
                ite,
                set1, set2
        );
    }

    private FunctionDeclaration addOrdNext(String prefix, Expression setExpression, FunctionDeclaration intMapping, Sig ordSig, Expression firstSet, ConstantDeclaration lastAtom)
    {
        String nextMapping = prefix + "nextMapping";

        FunctionDeclaration mapping     = new FunctionDeclaration(nextMapping, translator.atomSort, translator.atomSort);
        translator.addFunction(mapping);

        VariableDeclaration x = new VariableDeclaration("_x", translator.atomSort);
        VariableDeclaration y = new VariableDeclaration("_y", translator.atomSort);

        // for all x : x is a member implies intMapping(x) < intMapping (nextMapping(x)) and
        //                                                    x != lastAtom implies nextMapping(x) is a member

        BinaryExpression xMember = new BinaryExpression(TranslatorUtils.getTuple(x), BinaryExpression.Op.MEMBER, setExpression);
        BinaryExpression xLessThanNext = new BinaryExpression(
                new FunctionCallExpression(intMapping, x.getConstantExpr()),
                BinaryExpression.Op.LT,
                new FunctionCallExpression(intMapping,
                        new FunctionCallExpression(mapping, x.getConstantExpr())));

        Expression notXEqualsLast = new UnaryExpression(UnaryExpression.Op.NOT,
                new BinaryExpression(x.getConstantExpr(), BinaryExpression.Op.EQ, lastAtom.getConstantExpr()));
        Expression nextIsMember = new BinaryExpression(
                TranslatorUtils.getTuple(new FunctionCallExpression(mapping, x.getConstantExpr())),
                BinaryExpression.Op.MEMBER, setExpression);

        Expression impliesNextIsMember = new BinaryExpression(notXEqualsLast, BinaryExpression.Op.IMPLIES, nextIsMember);

        Expression xMemberconsequent = new BinaryExpression(xLessThanNext,BinaryExpression.Op.AND, impliesNextIsMember);

        Expression xMemberImplies = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, xMemberconsequent);

        Expression forAllX = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, xMemberImplies, x);
        translator.smtProgram.addAssertion(
                new Assertion("For all x : x is a member implies (intMapping(x) < intMapping (nextMapping(x)) and " +
                        "(x != lastAtom implies nextMapping(x) is a member))", forAllX));

        // the next mapping is one-to-one (injective) members
        // for all x, y (x != y and x, y members) implies (nextMapping(x) != nextMapping(y)))
        Expression xEqualsY = new BinaryExpression(x.getConstantExpr(), BinaryExpression.Op.EQ, y.getConstantExpr());
        Expression notXEqualsY = new UnaryExpression(UnaryExpression.Op.NOT, xEqualsY);

        Expression xyMembers = new BinaryExpression(
                new BinaryExpression(
                        TranslatorUtils.getTuple(x),
                        BinaryExpression.Op.MEMBER,
                        setExpression
                ),
                BinaryExpression.Op.AND,
                new BinaryExpression(
                        TranslatorUtils.getTuple(y),
                        BinaryExpression.Op.MEMBER,
                        setExpression
                ));

        Expression antecedent = new BinaryExpression(notXEqualsY, BinaryExpression.Op.AND, xyMembers);

        Expression mappingXEqualsMappingY = new BinaryExpression(
                new FunctionCallExpression(mapping, x.getConstantExpr()),
                BinaryExpression.Op.EQ,
                new FunctionCallExpression(mapping, y.getConstantExpr()));

        Expression consequent = new UnaryExpression(UnaryExpression.Op.NOT, mappingXEqualsMappingY);

        Expression implies = new BinaryExpression(antecedent, BinaryExpression.Op.IMPLIES, consequent);

        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, x, y);

        translator.smtProgram.addAssertion(new Assertion(nextMapping + " is injective for members", forAll));

        FunctionDeclaration ordNext = new FunctionDeclaration(prefix + "next", translator.setOfBinaryAtomSort);
        translator.addFunction(ordNext);

        // for all x, y (x,y) in the next relation iff x, y are members and nextMapping(x) = y
        Expression xy = TranslatorUtils.getTuple(x, y);
        Expression xyInNext = new BinaryExpression(xy, BinaryExpression.Op.MEMBER, ordNext.getConstantExpr());

        Expression xLessThanY = new BinaryExpression(
                new FunctionCallExpression(intMapping, x.getConstantExpr()),
                BinaryExpression.Op.LT,
                new FunctionCallExpression(intMapping, y.getConstantExpr()));

        Expression nextXEqualsY =  new BinaryExpression(
                new FunctionCallExpression(mapping, x.getConstantExpr()),
                BinaryExpression.Op.EQ,
                y.getConstantExpr());

        Expression  and = new BinaryExpression(xyMembers, BinaryExpression.Op.AND, nextXEqualsY);

        BinaryExpression iff = new BinaryExpression(xyInNext, BinaryExpression.Op.EQ, and);

        QuantifiedExpression forAllXY = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, iff,x, y);
        translator.smtProgram.addAssertion(new Assertion(prefix + "next", forAllXY));

        Expression ordSigExpression = translator.signaturesMap.get(ordSig).getConstantExpr();

        Sig.Field nextField = StreamSupport
                .stream(ordSig.getFields().spliterator(), false)
                .filter(field -> field.label.contains("Next"))
                .findFirst().get();

        Expression nextFieldExpression = translator.fieldsMap.get(nextField).getConstantExpr();

        Expression join = new BinaryExpression(ordSigExpression, BinaryExpression.Op.JOIN, nextFieldExpression);

        Expression equality = new BinaryExpression(ordNext.getConstantExpr(), BinaryExpression.Op.EQ, join);

        // next = ordSig.Next
        translator.smtProgram.addAssertion(
                new Assertion(ordNext.getName() + " = " + ordSig.label + "." + nextField.label, equality));

        // either (next is an empty set and the ordered set is a singleton) or next is nonempty
        Expression emptySet = new UnaryExpression(UnaryExpression.Op.EMPTYSET, translator.setOfBinaryAtomSort);
        Expression nextIsEmpty = new BinaryExpression(ordNext.getConstantExpr(), BinaryExpression.Op.EQ, emptySet);
        Expression setSingleton = new BinaryExpression(setExpression, BinaryExpression.Op.EQ, firstSet);
        Expression nextIsNonempty = new UnaryExpression(UnaryExpression.Op.NOT, nextIsEmpty);
        Expression or = new BinaryExpression(
                new BinaryExpression(nextIsEmpty, BinaryExpression.Op.AND, setSingleton)
                , BinaryExpression.Op.OR,
                nextIsNonempty);

        // either (next is an empty set and the ordered set is a singleton) or next is nonempty
        translator.smtProgram.addAssertion(
                new Assertion("either (next is an empty set and the ordered set is a singleton) or next is nonempty", or));
        return ordNext;
    }

    private FunctionDeclaration addOrdPrev(String prefix, FunctionDeclaration ordNext)
    {
        FunctionDeclaration ordPrev = new FunctionDeclaration(prefix + "prev", translator.setOfBinaryAtomSort);

        UnaryExpression transpose = new UnaryExpression(UnaryExpression.Op.TRANSPOSE, ordNext.getConstantExpr());

        BinaryExpression equality = new BinaryExpression(ordPrev.getConstantExpr(),
                BinaryExpression.Op.EQ, transpose);

        translator.addFunction(ordPrev);

        translator.smtProgram.addAssertion(new Assertion(prefix + "PrevAuxiliary", equality));

        return ordPrev;
    }

    private FunctionDefinition getComparisonDefinition(String prefix, String suffix, FunctionDeclaration mapping, VariableDeclaration set1, VariableDeclaration set2, VariableDeclaration element1, VariableDeclaration element2, BinaryExpression.Op operator)
    {
        QuantifiedExpression ltExpression =
                new QuantifiedExpression
                (
                    QuantifiedExpression.Op.FORALL,
                            new BinaryExpression
                            (
                                new BinaryExpression
                                (
                                    new BinaryExpression
                                    (
                                        TranslatorUtils.getTuple(element1),
                                        BinaryExpression.Op.MEMBER,
                                        set1.getConstantExpr()
                                    ),
                                    BinaryExpression.Op.AND,
                                    new BinaryExpression
                                    (
                                        TranslatorUtils.getTuple(element2),
                                        BinaryExpression.Op.MEMBER,
                                        set2.getConstantExpr()
                                    )
                                ),
                                BinaryExpression.Op.IMPLIES,
                                new BinaryExpression
                                (
                                    new FunctionCallExpression(mapping, element1.getConstantExpr()),
                                    operator,
                                    new FunctionCallExpression(mapping, element1.getConstantExpr())
                                )
                            ),
                    element1, element2
                );

        return new FunctionDefinition(prefix + suffix,
                new BoolSort(),
                ltExpression,
                set1, set2
        );
    }
}
