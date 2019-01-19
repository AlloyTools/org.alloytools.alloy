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
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup.getName(), constDecl.getConstantExpr()));
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
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup.getName(), constDecl.getConstantExpr()));
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
            expr = translator.exprTranslator.mkSingletonOutOfTuple(new FunctionCallExpression(translator.valueOfUnaryIntTup.getName(), constDecl.getConstantExpr()));
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
        translator.smtProgram.addFunctionDeclaration(translator.intUniv);
        translator.smtProgram.addAssertion(new Assertion(eqExpr));           
    }


    private FunctionDeclaration declareUnaryAtomFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryAtomSort);
            translator.smtProgram.addFunctionDeclaration(declaration);
        }
        return declaration;
    }
    
    private FunctionDeclaration declareUnaryIntFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, translator.setOfUnaryIntSort);
            translator.smtProgram.addFunctionDeclaration(declaration);
        }
        return declaration;
    }    

    public void translateSigs()
    {
        collectReachableSigs();
        translateSignatures();
        translateSignatureHierarchies();
        this.fieldTranslator.translateFields();
        translateSigFacts();
    }
    
    private void translateSigFacts()
    {
        // Translate facts on signatures
        for(Map.Entry<Sig, Expr> sigFact : translator.sigFacts.entrySet())
        {
            String bdVarName = "this";
            Map<BoundVariableDeclaration, Expression> boundVariables = new HashMap<>();
            BoundVariableDeclaration bdVar = new BoundVariableDeclaration(bdVarName, translator.atomSort);
            boundVariables.put(bdVar, translator.signaturesMap.get(sigFact.getKey()).getConstantExpr());
            Expression member = translator.exprTranslator.getMemberExpression(boundVariables, 0);
            Map<String, Expression> variablesScope = new HashMap<>();

            variablesScope.put(bdVarName, new ConstantExpression(new FunctionDeclaration(bdVarName, translator.atomSort)));

            Expr       expr     = sigFact.getValue();

            // handle total order operator differently
            if(expr instanceof ExprUnary &&
                    ((ExprUnary) expr).sub instanceof ExprList &&
                    ((ExprList) ((ExprUnary) expr).sub).op == ExprList.Op.TOTALORDER)
            {
                translateTotalOrder(sigFact.getKey(), ((ExprList) ((ExprUnary) expr).sub), variablesScope);
                continue;
            }

            Expression bodyExpr = translator.exprTranslator.translateExpr(sigFact.getValue(), variablesScope);

            translator.smtProgram.addAssertion(new Assertion("Fact for sig: " + sigFact.getKey(), new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), new BinaryExpression(member, BinaryExpression.Op.IMPLIES, bodyExpr))));
        }        
    }

    //ToDo: refactor this method
    private void translateTotalOrder(Sig ordSig, ExprList exprList, Map<String, Expression> variablesScope)
    {
        if(exprList.args.size() != 3)
        {
            throw new UnsupportedOperationException();
        }

        Expr       set              = exprList.args.get(0);
        Expr       first            = exprList.args.get(1);

        // define a new uninterpreted one-to-one mapping from the signature to integers
        String              label       = ordSig.label;
        // convert ordA/Ord to ordA_
        String              prefix      = label.replaceFirst("/Ord", "_");
        String              mappingName = TranslatorUtils.sanitizeName(prefix + "IntMap");
        FunctionDeclaration mapping     = new FunctionDeclaration(mappingName, translator.atomSort, translator.intSort);
        translator.smtProgram.addFunctionDeclaration(mapping);

        Expression setExpression    = translator.exprTranslator.translateExpr(set, variablesScope);
        Expression firstExpression  = translator.exprTranslator.translateExpr(first, variablesScope);

        // ordering/first
        Expression firstSet         = defineFirstElement(prefix, firstExpression, mappingName);

        // ordering/last
        Expression lastSet          = defineLastElement(prefix, mappingName, setExpression);

        // Next relation
        ConstantDeclaration ordNext =  addOrdNext(prefix,setExpression, mappingName, ordSig, firstSet);

        // prev relation
        ConstantDeclaration ordPrev = addOrdPrev(prefix,setExpression, mappingName, ordNext);

        BoundVariableDeclaration set1 = new BoundVariableDeclaration("s1", translator.setOfUnaryAtomSort);
        BoundVariableDeclaration set2 = new BoundVariableDeclaration("s2", translator.setOfUnaryAtomSort);

        BoundVariableDeclaration element1 = new BoundVariableDeclaration("e1", translator.atomSort);
        BoundVariableDeclaration element2 = new BoundVariableDeclaration("e2", translator.atomSort);

        // ordering/prevs
        FunctionDefinition prevs = getPrevsNextsDefinition(prefix, set1, ordPrev, "prevs");
        translator.smtProgram.addFunctionDefinition(prevs);

        // ordering/nexts
        FunctionDefinition nexts = getPrevsNextsDefinition(prefix, set1, ordNext, "nexts");
        translator.smtProgram.addFunctionDefinition(nexts);

        // ordering/lt
        FunctionDefinition lt = getComparisonDefinition(prefix, "lt", mappingName, set1, set2, element1, element2, BinaryExpression.Op.LT);
        translator.smtProgram.addFunctionDefinition(lt);

        // ordering/gt
        FunctionDefinition gt = getComparisonDefinition(prefix, "gt", mappingName, set1, set2, element1, element2, BinaryExpression.Op.GT);
        translator.smtProgram.addFunctionDefinition(gt);

        // ordering/lte
        FunctionDefinition lte = getComparisonDefinition(prefix, "lte", mappingName, set1, set2, element1, element2, BinaryExpression.Op.LTE);
        translator.smtProgram.addFunctionDefinition(lte);

        // ordering/gte
        FunctionDefinition gte = getComparisonDefinition(prefix, "gte", mappingName, set1, set2, element1, element2, BinaryExpression.Op.GTE);
        translator.smtProgram.addFunctionDefinition(gte);

        //ordering/larger
        FunctionDefinition larger = getLargerSmallerDefinition(prefix, "larger", set1, set2, gt);
        translator.smtProgram.addFunctionDefinition(larger);

        //ordering/smaller
        FunctionDefinition smaller = getLargerSmallerDefinition(prefix, "smaller", set1, set2, lt);
        translator.smtProgram.addFunctionDefinition(smaller);

        //ordering/max
        FunctionDefinition max = getMaxMinDefinition(prefix, "max", set1, ordPrev);
        translator.smtProgram.addFunctionDefinition(max);

        //ordering/min
        FunctionDefinition min = getMaxMinDefinition(prefix, "min", set1, ordNext);
        translator.smtProgram.addFunctionDefinition(min);
    }

    private Expression defineFirstElement(String prefix, Expression firstExpression, String mappingName)
    {
        final String suffix = "first";
        ConstantDeclaration firstAtom   = new ConstantDeclaration(TranslatorUtils.getNewAtomName(), translator.atomSort);
        ConstantDeclaration first       = new ConstantDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression          firstSet    = new UnaryExpression(UnaryExpression.Op.SINGLETON,
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getConstantExpr()));

        translator.smtProgram.addConstantDeclaration(firstAtom);
        translator.smtProgram.addConstantDeclaration(first);

        // there is only one first element
        // ordering/first = (singleton (maketuple firstAtom))
        Expression firstSingleton       = new BinaryExpression(first.getConstantExpr(), BinaryExpression.Op.EQ, firstSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + "(singleton (maketuple firstAtom))", firstSingleton));

        // ordering/first = ordering/Ord.First
        Expression ordFirstSingleton    = new BinaryExpression(first.getConstantExpr(), BinaryExpression.Op.EQ, firstExpression);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + " = " + prefix + "Ord.First", ordFirstSingleton));

        // each element is greater than or equal to the first element
        BoundVariableDeclaration x = new BoundVariableDeclaration("x", translator.atomSort);
        Expression gte = new BinaryExpression(
                new FunctionCallExpression(mappingName, x.getConstantExpr()),
                BinaryExpression.Op.GTE,
                new FunctionCallExpression(mappingName, firstAtom.getConstantExpr()));
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, gte, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is greater than or equal to the first element", forAll));

        return firstSet;
    }

    private Expression defineLastElement(String prefix, String mappingName, Expression setExpression)
    {
        final String suffix = "last";
        ConstantDeclaration lastAtom   = new ConstantDeclaration(TranslatorUtils.getNewAtomName(), translator.atomSort);
        ConstantDeclaration last       = new ConstantDeclaration(prefix + suffix, translator.setOfUnaryAtomSort);

        Expression          lastSet    = new UnaryExpression(UnaryExpression.Op.SINGLETON,
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getConstantExpr()));

        translator.smtProgram.addConstantDeclaration(lastAtom);
        translator.smtProgram.addConstantDeclaration(last);


        // last element is a member of the set
        Expression member = new BinaryExpression(
                new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, lastAtom.getConstantExpr()),
                BinaryExpression.Op.MEMBER,
                setExpression);
        translator.smtProgram.addAssertion(new Assertion ("last element is a member", member));

        // there is only one last element
        // ordering/last = (singleton (maketuple lastAtom))
        Expression lastSingleton       = new BinaryExpression(last.getConstantExpr(), BinaryExpression.Op.EQ, lastSet);
        translator.smtProgram.addAssertion(new Assertion(prefix + suffix + "(singleton (maketuple lastAtom))", lastSingleton));

        // each element is less than or equal to the last element
        BoundVariableDeclaration x = new BoundVariableDeclaration("x", translator.atomSort);
        Expression gte = new BinaryExpression(
                new FunctionCallExpression(mappingName, x.getConstantExpr()),
                BinaryExpression.Op.LTE,
                new FunctionCallExpression(mappingName, lastAtom.getConstantExpr()));
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, gte, x);
        translator.smtProgram.addAssertion(new Assertion(
                "each element is less than or equal to the last element", forAll));

        return lastSet;
    }

    private FunctionDefinition getMaxMinDefinition(String prefix, String suffix, BoundVariableDeclaration set, ConstantDeclaration declaration)
    {
        Expression tClosure     = new UnaryExpression(UnaryExpression.Op.TCLOSURE, declaration.getConstantExpr());

        Expression join         = new BinaryExpression(set.getConstantExpr(), BinaryExpression.Op.JOIN, tClosure);

        Expression difference   = new BinaryExpression(set.getConstantExpr(), BinaryExpression.Op.SETMINUS, join);

        return new FunctionDefinition(prefix + suffix, translator.setOfUnaryAtomSort,
                difference, set);
    }

    private FunctionDefinition getPrevsNextsDefinition(String prefix, BoundVariableDeclaration set1, ConstantDeclaration ord, String suffix)
    {
        UnaryExpression tClosure = new UnaryExpression(UnaryExpression.Op.TCLOSURE, ord.getConstantExpr());
        BinaryExpression join = new BinaryExpression(set1.getConstantExpr(), BinaryExpression.Op.JOIN, tClosure);
        String name = prefix + suffix;
        FunctionDefinition definition = new FunctionDefinition(name, translator.setOfUnaryAtomSort, join, set1);
        return definition;
    }

    private FunctionDefinition getLargerSmallerDefinition(String prefix, String suffix, BoundVariableDeclaration set1, BoundVariableDeclaration set2, FunctionDefinition definition)
    {
        FunctionCallExpression call = new FunctionCallExpression(definition.funcName, set1.getConstantExpr(), set2.getConstantExpr());
        ITEExpression ite = new ITEExpression(call, set1.getConstantExpr(),
                set2.getConstantExpr());
        return new FunctionDefinition(prefix + suffix,
                translator.setOfUnaryAtomSort,
                ite,
                set1, set2
        );
    }

    private ConstantDeclaration addOrdNext(String prefix, Expression setExpression, String mappingName, Sig ordSig, Expression firstSet)
    {
        ConstantDeclaration ordNext = new ConstantDeclaration(prefix + "next", translator.setOfBinaryAtomSort);

        BoundVariableDeclaration x = new BoundVariableDeclaration("_x", translator.atomSort);
        BoundVariableDeclaration y = new BoundVariableDeclaration("_y", translator.atomSort);
        BoundVariableDeclaration z = new BoundVariableDeclaration("_z", translator.atomSort);

        // x, y in setExpression implies
        // ((x, y) in Ord_Next) iff (x < y and for all z. (z in setExpression implies x < z and y <= z))

        BinaryExpression xyMembers = new BinaryExpression(
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

        Expression xy = TranslatorUtils.getTuple(x, y);
        BinaryExpression xyInNext = new BinaryExpression(xy, BinaryExpression.Op.MEMBER, ordNext.getConstantExpr());

        BinaryExpression zMember = new BinaryExpression(TranslatorUtils.getTuple(z), BinaryExpression.Op.MEMBER, setExpression);

        BinaryExpression xLessThanY = new BinaryExpression(
                new FunctionCallExpression(mappingName, x.getConstantExpr()),
                BinaryExpression.Op.LT,
                new FunctionCallExpression(mappingName, y.getConstantExpr()));

        BinaryExpression xLessThanZ = new BinaryExpression(
                new FunctionCallExpression(mappingName, x.getConstantExpr()),
                BinaryExpression.Op.LT,
                new FunctionCallExpression(mappingName, z.getConstantExpr()));

        BinaryExpression yLessEqualsZ = new BinaryExpression(
                new FunctionCallExpression(mappingName, y.getConstantExpr()),
                BinaryExpression.Op.LTE,
                new FunctionCallExpression(mappingName, z.getConstantExpr()));

        BinaryExpression zImplies = new BinaryExpression
                (
                    new BinaryExpression(
                    zMember,
                    BinaryExpression.Op.AND,
                    xLessThanZ)
                    ,BinaryExpression.Op.IMPLIES,
                    yLessEqualsZ
                );

        QuantifiedExpression forAllZ = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, zImplies, z);

        BinaryExpression xLessThanYAndForAllZ = new BinaryExpression(xLessThanY, BinaryExpression.Op.AND, forAllZ);

        BinaryExpression iff = new BinaryExpression(xyInNext, BinaryExpression.Op.EQ, xLessThanYAndForAllZ);

        BinaryExpression xyImplies = new BinaryExpression(xyMembers, BinaryExpression.Op.IMPLIES, iff);

        QuantifiedExpression forAllXY = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, xyImplies,x, y);

        translator.smtProgram.addConstantDeclaration(ordNext);

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
        Expression and = new BinaryExpression(nextIsEmpty, BinaryExpression.Op.EQ, setSingleton);
        Expression nextIsNonempty = new UnaryExpression(UnaryExpression.Op.NOT, nextIsEmpty);
        Expression or = new BinaryExpression(and, BinaryExpression.Op.OR, nextIsNonempty);

        // either (next is an empty set and the ordered set is a singleton) or next is nonempty
        translator.smtProgram.addAssertion(
                new Assertion("either (next is an empty set and the ordered set is a singleton) or next is nonempty", or));
        return ordNext;
    }

    private ConstantDeclaration addOrdPrev(String prefix, Expression setExpression, String mappingName, ConstantDeclaration ordNext)
    {
        ConstantDeclaration ordPrev = new ConstantDeclaration(prefix + "prev", translator.setOfBinaryAtomSort);

        UnaryExpression transpose = new UnaryExpression(UnaryExpression.Op.TRANSPOSE, ordNext.getConstantExpr());

        BinaryExpression equality = new BinaryExpression(ordPrev.getConstantExpr(),
                BinaryExpression.Op.EQ, transpose);

        translator.smtProgram.addConstantDeclaration(ordPrev);

        translator.smtProgram.addAssertion(new Assertion(prefix + "PrevAuxiliary", equality));

        return ordPrev;
    }

    private FunctionDefinition getComparisonDefinition(String prefix, String suffix, String mappingName, BoundVariableDeclaration set1, BoundVariableDeclaration set2, BoundVariableDeclaration element1, BoundVariableDeclaration element2, BinaryExpression.Op operator)
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
                                    new FunctionCallExpression(mappingName, element1.getConstantExpr()),
                                    operator,
                                    new FunctionCallExpression(mappingName, element1.getConstantExpr())
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
