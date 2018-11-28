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
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.smtAst.*;
import java.util.ArrayList;
import java.util.HashMap;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SignatureTranslator
{

    private final Alloy2SMTTranslator translator;
    private final FieldTranslator fieldTranslator;

    public SignatureTranslator(Alloy2SMTTranslator translator)
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

            UnaryExpression emptySet   = new UnaryExpression(UnaryExpression.Op.EMPTYSET, translator.signaturesMap.get(signatures.get(i)).getSort());

            for (int j = i + 1 ; j < signatures.size(); j++)
            {
                Expression          right       = translator.signaturesMap.get(signatures.get(j)).getConstantExpr();
                BinaryExpression    disjoint    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);
                BinaryExpression    equality    = new BinaryExpression(disjoint, BinaryExpression.Op.EQ, emptySet);

                translator.smtProgram.addAssertion(new Assertion(equality));
            }
        }
    }

    private void collectReachableSigs()
    {
        for(Sig sig : translator.alloyModel.getAllSigs())
        {
            if(sig.isTopLevel())
            {
                translator.topLevelSigs.add(sig);
            }
            translator.reachableSigs.add(sig);
        }
    }
    
    private void translateSignatures()
    {
        translator.reachableSigs.forEach((sig) ->
        {
            if(sig.type().is_int())
            {
                FunctionDeclaration functionDeclaration = declareUnaryIntFunction(TranslatorUtils.sanitizeName(sig.toString()));
                translator.signaturesMap.put(sig, functionDeclaration);                
            }
            else
            {
                FunctionDeclaration functionDeclaration =  declareUnaryAtomFunction(TranslatorUtils.sanitizeName(sig.toString()));
                translator.signaturesMap.put(sig, functionDeclaration);
            }              
        });
        translator.reachableSigs.forEach((sig) ->
        {
            FunctionDeclaration functionDeclaration = translator.signaturesMap.get(sig);                       

            // if sig extends another signature
            if(!sig.isTopLevel())
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
            for(Sig.Field field : sig.getFields())
            {
                this.fieldTranslator.fields.add(field);
            }
            for(Expr expr : sig.getFacts())
            {
                translator.sigFacts.put(sig, expr);
            }
        });        
        //ToDo: important review the logic for cardinality in the case of
        // top level signatures and the case of subset signatures.
        //translateDisjointSignatures(translator.topLevelSigs);
    }

    private void translateSignatureOneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = TranslatorUtils.generateAuxiliarySetNAtoms(1, 1, translator);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.EQ, declaration.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureLoneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = TranslatorUtils.generateAuxiliarySetNAtoms(1, 1, translator);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.SUBSET, declaration.getConstantExpr());
        translator.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureSomeMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = translator.signaturesMap.get(sig);

        FunctionDeclaration declaration = TranslatorUtils.generateAuxiliarySetNAtoms(1, 1, translator);

        BinaryExpression subset   = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.SUBSET, signature.getConstantExpr());
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
                if(parentSig == Sig.SIGINT && !translator.signaturesMap.containsKey(parentSig))
                {
                    declareIntSig();
                }
                FunctionDeclaration parentDeclaration   = translator.signaturesMap.get(parentSig);
                BinaryExpression    subset              = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
                translator.smtProgram.addAssertion(new Assertion(subset));                     
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
            Expression bodyExpr = translator.exprTranslator.translateExpr(sigFact.getValue(), variablesScope);

            translator.smtProgram.addAssertion(new Assertion("Fact for sig: " + sigFact.getKey(), new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(boundVariables.keySet()), new BinaryExpression(member, BinaryExpression.Op.IMPLIES, bodyExpr))));
        }        
    }
}
