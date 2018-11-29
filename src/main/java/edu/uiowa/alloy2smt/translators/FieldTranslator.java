/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.smtAst.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class FieldTranslator
{

    private final Alloy2SMTTranslator translator;
    public  List<Sig.Field> fields = new ArrayList<>();

    public FieldTranslator(Alloy2SMTTranslator translator)
    {
        this.translator = translator;
    }

    void translateFields()
    {
        for(Sig.Field f : this.fields)
        {
            translate(f);
        }
    }
    
    void collectFieldComponentExprs(Expr expr, List<Expr> fieldComponentExprs)
    {
        if(expr instanceof ExprUnary)
        {            
            if(((ExprUnary) expr).sub instanceof Sig)
            {
                fieldComponentExprs.add(((ExprUnary) expr).sub);
            }
            else if(((ExprUnary) expr).sub instanceof Sig.Field)
            {
                collectFieldComponentExprs(((Sig.Field)((ExprUnary) expr).sub).decl().expr, fieldComponentExprs);
            }
            else if(((ExprUnary) expr).sub instanceof ExprUnary)
            {
                collectFieldComponentExprs((ExprUnary)(((ExprUnary) expr).sub), fieldComponentExprs);
            }
            else if(((ExprUnary) expr).sub instanceof ExprVar)
            {
                //skip, ((ExprUnary) expr).sub = this
            }   
            else if(((ExprUnary) expr).sub instanceof ExprBinary)
            {
                if(isArrowRelated(((ExprBinary)((ExprUnary) expr).sub)))
                {
                    collectFieldComponentExprs(((ExprBinary)((ExprUnary) expr).sub).left, fieldComponentExprs);
                    collectFieldComponentExprs(((ExprBinary)((ExprUnary) expr).sub).right, fieldComponentExprs);                    
                }
                else
                {
                   fieldComponentExprs.add(((ExprUnary) expr).sub);
                }
            }            
            else
            {
                throw new UnsupportedOperationException("Something we have not supported yet: " + ((ExprUnary) expr).sub);
            }
        }
        else if(expr instanceof ExprBinary)
        {
                if(isArrowRelated((ExprBinary)expr))
                {
                    collectFieldComponentExprs(((ExprBinary)expr).left, fieldComponentExprs);
                    collectFieldComponentExprs(((ExprBinary)expr).right, fieldComponentExprs);             
                }
                else
                {
                   fieldComponentExprs.add((ExprBinary) expr);
                }            
        }
        else 
        {
            throw new UnsupportedOperationException();
        }
    }
    
    void translate(Sig.Field field)
    {

        String      fieldName   = TranslatorUtils.sanitizeName(field.sig.label + "/" + field.label);
        List<Sort>  fieldSorts  = new ArrayList<>();

        // a field relation is a subset of the product of some signatures        
        List<Expr> fieldComponentExprs = new ArrayList<>();
        
        fieldComponentExprs.add(field.sig);
        
        // Collect component of the field
        collectFieldComponentExprs(field.decl().expr, fieldComponentExprs);
        
        /* alloy: sig Book{addr: Name -> lone Addr}
         *  smt  : (assert (subset addr (product (product Book Name) Addr)))
         */
        Expression  first   = translator.signaturesMap.get(field.sig).getConstantExpr();
        Expression  second  = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>());
        BinaryExpression    product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldComponentExprs.size(); i++)
        {       
            Expression  expr  = (fieldComponentExprs.get(i) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(i)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(i), new HashMap<>());            
            product = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);            
        }
        // Collect field's type information
        for(int i = 0; i < fieldComponentExprs.size(); i++)
        {
            if(fieldComponentExprs.get(i).type().is_int())
            {
                fieldSorts.add(translator.intSort);
            }
            else
            {
                fieldSorts.add(translator.atomSort);
            }
        }        
        
      
        FunctionDeclaration fieldDecl = new FunctionDeclaration(fieldName, new SetSort(new TupleSort(fieldSorts)));
        // declare a variable for the field
        translator.smtProgram.addFunctionDeclaration(fieldDecl);
        translator.fieldsMap.put(field, fieldDecl);   
        // make a subset assertion
        translator.smtProgram.addAssertion(new Assertion(new BinaryExpression(fieldDecl.getConstantExpr(), BinaryExpression.Op.SUBSET, product)));
        
        // translateExpr multiplicities and remove the first field Sig in fieldComponentExprs
        fieldComponentExprs.remove(0);
        translateMultiplicities(field, fieldComponentExprs);
    }

    private void translateMultiplicities(Sig.Field field, List<Expr> fieldComponentExprs)
    {
        Expr expr = field.decl().expr;
        
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary) expr;
            
            if(fieldComponentExprs.size() > 1)
            {
                throw new UnsupportedOperationException("We currenty do not support multiplicity constraints on nested relations!");
            }             
            switch (exprUnary.op)
            {
                case SOMEOF     : translateRelationSomeMultiplicity(field, fieldComponentExprs);break;
                case LONEOF     : translateRelationLoneMultiplicity(field, fieldComponentExprs);break;
                case ONEOF      : translateRelationOneMultiplicity(field, fieldComponentExprs);break;
                case SETOF      : break; // no assertion needed
                case EXACTLYOF  : break; //ToDo: review translator case
                default:
                {
                    throw new UnsupportedOperationException("Not supported yet");
                }
            }
        }
        else if (expr instanceof ExprBinary)
        {
            translateBinaryMultiplicities((ExprBinary) expr, field, fieldComponentExprs);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateNestedMultiplicities(ExprBinary exprBinary, Sig.Field field)
    {
        switch (exprBinary.op)
        {
            case ARROW : break;
            default:
            {
                throw new UnsupportedOperationException();
            }
        }
    }    
    
    
    private void translateBinaryMultiplicities(ExprBinary exprBinary, Sig.Field field, List<Expr> fieldComponentExprs)
    {
        if(fieldComponentExprs.size() > 2)
        {
            throw new UnsupportedOperationException("Currently, we do not support multiplicity constraints on relations with arity GT 3!");
        }        

        switch (exprBinary.op)
        {
            case ARROW              : break;
            case ANY_ARROW_SOME     : translateAnyArrowSome(fieldComponentExprs, field); break;
            case ANY_ARROW_ONE      : translateAnyArrowOne(fieldComponentExprs, field); break;
            case ANY_ARROW_LONE     : translateAnyArrowLone(fieldComponentExprs, field); break;
            case SOME_ARROW_ANY     : translateSomeArrowAny(fieldComponentExprs, field); break;
            case SOME_ARROW_SOME    : 
            {
                translateAnyArrowSome(fieldComponentExprs, field);
                translateSomeArrowAny(fieldComponentExprs, field); break;
            }
            case SOME_ARROW_ONE     : 
            {
                translateAnyArrowOne(fieldComponentExprs, field); 
                translateSomeArrowAny(fieldComponentExprs, field); break;
            }
            case SOME_ARROW_LONE    : 
            {
                translateAnyArrowLone(fieldComponentExprs, field);
                translateSomeArrowAny(fieldComponentExprs, field); break;
            }
            case ONE_ARROW_ANY      : translateOneArrowAny(fieldComponentExprs, field); break;
            case ONE_ARROW_SOME     : 
            {
                translateAnyArrowSome(fieldComponentExprs, field);
                translateOneArrowAny(fieldComponentExprs, field); break;
            }
            case ONE_ARROW_ONE      : 
            {
                translateOneArrowAny(fieldComponentExprs, field); 
                translateAnyArrowOne(fieldComponentExprs, field); break;
            }
            case ONE_ARROW_LONE     : 
            {
                translateOneArrowAny(fieldComponentExprs, field); 
                translateAnyArrowLone(fieldComponentExprs, field); break;
            }
            case LONE_ARROW_ANY     : translateLoneArrowAny(fieldComponentExprs, field); break;
            case LONE_ARROW_SOME    : 
            {
                translateAnyArrowSome(fieldComponentExprs, field);
                translateLoneArrowAny(fieldComponentExprs, field); break;
            }
            case LONE_ARROW_ONE     : 
            {
                translateLoneArrowAny(fieldComponentExprs, field); 
                translateAnyArrowOne(fieldComponentExprs, field); break;
            }
            case LONE_ARROW_LONE    : 
            {
                translateAnyArrowLone(fieldComponentExprs, field); 
                translateLoneArrowAny(fieldComponentExprs, field); break;
            }
            case ISSEQ_ARROW_LONE   : throw new UnsupportedOperationException();
            default:
            {
                throw new UnsupportedOperationException();
            }
        }
    }
    
    private void translateArrow(ExprBinary exprBinary, Expression joinExpr, List<Sig> fieldSignatures, Sig.Field field, List<BoundVariableDeclaration> bdVars)
    {
        int numOfSigs   = fieldSignatures.size();
        int leftArity   = exprBinary.left.type().arity();
        int rightArity  = exprBinary.right.type().arity();
        
        List<BoundVariableDeclaration> newBdVars = new ArrayList<>();
        newBdVars.addAll(bdVars);

        if(leftArity > 1)
        {            
            String  sigVarName  = TranslatorUtils.getNewName();
            Sort    sigVarSort  = field.sig.type().is_int()?translator.intSort:translator.atomSort;  
            BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, sigVarSort);
            Expression                  fieldExpr   = translator.fieldsMap.get(field).getConstantExpr(); 
            joinExpr = new BinaryExpression(mkSinletonOutofAtoms(sigVar.getConstantExpr()), BinaryExpression.Op.JOIN, fieldExpr);
            
            translateNestedMultiplicities((ExprBinary)exprBinary.left, field);
        }
    }

    // ANY_ARROW_SOME
    private void translateAnyArrowSome(List<Expr> fieldComponentExprs, Sig.Field field)
    {   
        int numOfSigs   = fieldComponentExprs.size();
//        int leftArity   = exprBinary.left.type().arity();
//        int rightArity  = exprBinary.right.type().arity();
        
        if(numOfSigs == 2)
        {
            String sigVarName       = TranslatorUtils.getNewName();
            String fstSigVarName    = TranslatorUtils.getNewName();
            String sndSigVarName    = TranslatorUtils.getNewName();

            Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
            Sort fstSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;
            Sort sndSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;          

            BoundVariableDeclaration    sigVar  = new BoundVariableDeclaration(sigVarName, sigVarSort);
            BoundVariableDeclaration fstSigVar  = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
            BoundVariableDeclaration sndSigVar  = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);

            Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
            Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
            Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>()); 
            Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 

            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                                BinaryExpression.Op.MEMBER, sigExpr);
            Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, fstSigExpr); 
            Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, sndSigExpr);  
            Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                                BinaryExpression.Op.MEMBER, fieldExpr);        
            sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

            QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, sndSigVarMembership, sndSigVar);
            QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
            QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

            translator.smtProgram.addAssertion(new Assertion(outerForall));            
        }
//        else
//        {
//            String sigVarName       = TranslatorUtils.getNewName();
//            String fstSigVarName    = TranslatorUtils.getNewName();
//            String sndSigVarName    = TranslatorUtils.getNewName();
//            
//            String leftSetName      = TranslatorUtils.getNewSetName();
//            String rightSetName     = TranslatorUtils.getNewSetName();
//
//            Sort                        sigVarSort  = field.sig.type().is_int()?translator.intSort:translator.atomSort;
//            BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, sigVarSort);
//            
//            Sort fstSigVarSort;
//            Sort sndSigVarSort;
//            
//            Expression leftSigExpr;
//            Expression rightSigExpr;
//            
//            BoundVariableDeclaration fstSigVar;
//            BoundVariableDeclaration sndSigVar;
//
//            Expression fstSigVarMembership;
//            Expression sndSigVarMembership;
//            Expression fieldMembership;
//
//            Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
//            Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
//            
//            
//            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
//                                                                BinaryExpression.Op.MEMBER, sigExpr);         
//            Expression sigVarSet            = mkSinletonOutofAtoms(sigVar.getConstantExpr());
//            
//            if(leftArity > 1)
//            {
//                List<Sort> elementSorts = new ArrayList<>();
//                
//                for(int i = 0; i < leftArity && i < numOfSigs; ++i)
//                {
//                    Sort s  = fieldSignatures.get(i).type().is_int()?translator.intSort:translator.atomSort;
//                    elementSorts.add(s);
//                }
//                fstSigVarSort = new TupleSort(elementSorts);
//                FunctionDeclaration varDecl = new FunctionDeclaration(leftSetName, new SetSort(fstSigVarSort));                                
//                leftSigExpr = varDecl.getConstantExpr();
//                translator.smtProgram.addFcnDecl(varDecl);
//                fstSigVar           = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);                
//                fstSigVarMembership = new BinaryExpression(fstSigVar.getConstantExpr(),
//                                                                BinaryExpression.Op.MEMBER, leftSigExpr);  
//                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(fstSigVar.getConstantExpr()));
//                
//                // Translate left expression
//                translateNestedMultiplicities((ExprBinary)exprBinary.left, field);
//            }
//            else
//            {
//                leftSigExpr         = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
//                fstSigVarSort       = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
//                fstSigVar           = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
//                fstSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
//                                                                BinaryExpression.Op.MEMBER, leftSigExpr);
//                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(fstSigVar.getConstantExpr()));
//            }
//            
//            if(rightArity > 1)
//            {
//                List<Sort> elementSorts = new ArrayList<>();
//                
//                for(int i = leftArity; i < leftArity+rightArity && i < numOfSigs; ++i)
//                {
//                    Sort s  = fieldSignatures.get(i).type().is_int()?translator.intSort:translator.atomSort;
//                    elementSorts.add(s);
//                }                
//                sndSigVarSort = new TupleSort(elementSorts);   
//                FunctionDeclaration varDecl = new FunctionDeclaration(rightSetName, new SetSort(sndSigVarSort));
//                rightSigExpr = varDecl.getConstantExpr();
//                sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
//                sndSigVarMembership = new BinaryExpression(sndSigVar.getConstantExpr(),
//                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
//                translator.smtProgram.addFcnDecl(varDecl);
//                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(sndSigVar.getConstantExpr()));
//                // Translate right expression
//                translateNestedMultiplicities((ExprBinary)exprBinary.right, field);                              
//            }
//            else
//            {                
//                rightSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();             
//                sndSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
//                sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
//                sndSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
//                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
//                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(sndSigVar.getConstantExpr()));                
//            }
//
//            if(leftArity > 1 || rightArity > 1)
//            {
//                fieldMembership = new BinaryExpression(sigVarSet, BinaryExpression.Op.SUBSET, fieldExpr);                     
//            }
//            else
//            {
//                fieldMembership = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
//                                                                                BinaryExpression.Op.MEMBER, fieldExpr);                  
//            }
//           
//            sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
//
//            QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, sndSigVarMembership, sndSigVar);
//            QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
//            QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);
//
//            translator.smtProgram.addAssertion(new Assertion(outerForall));                 
//        }
        //ToDo: handle nested multiplicities
    }
    
    // SOME_ARROW_ANY
    private void translateSomeArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {   
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        
        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;  
        
        BoundVariableDeclaration    sigVar  = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration sndSigVar  = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration fstSigVar  = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();    
        // Change the order of fst and snd sig expressions        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>());         
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);  
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstSigVarMembership, fstSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sndSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }    
    
    // ONE_ARROW_ANY
    private void translateOneArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;            
        
        BoundVariableDeclaration    sigVar          = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar          = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar          = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar     = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();                
        Expression fstSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>());        
        Expression sndSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());   
        
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndSigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr(), fstSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerForall), sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }    
    
    // ANY_ARROW_ONE
    private void translateAnyArrowOne(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;          
        
        BoundVariableDeclaration    sigVar          = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar          = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar          = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar     = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>()); 
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerForall), sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }       
    
    private void translateAnyArrowLone(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;        
        
        BoundVariableDeclaration    sigVar          = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar          = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar          = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar     = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>()); 
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);       
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, 
                                                                        new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), sndSigVar);        
        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), sndSigVar);
        
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall)), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    } 
    
   private void translateLoneArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        String sigVarName           = TranslatorUtils.getNewName();
        String fstSigVarName        = TranslatorUtils.getNewName();
        String sndSigVarName        = TranslatorUtils.getNewName();
        String sndPrimeSigVarName   = TranslatorUtils.getNewName();
        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldComponentExprs.get(1).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldComponentExprs.get(0).type().is_int()?translator.intSort:translator.atomSort;
        
        BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar      = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1), new HashMap<>());        
        Expression sndSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());   
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndSigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);       
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, 
                                                                        new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), sndSigVar);        
        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr(), fstSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), sndSigVar);
        
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall)), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }     
    

    private void translateRelationSomeMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
    {
        //(assert
        //	(forall ((x Atom))
        //		(=> (member (mkTuple x) Book)
        //			(exists ((y Atom))
        //				(and
        //					(member (mkTuple y) Addr)
        //					(member (mkTuple x y) addr)
        //				)
        //			)
        //		)
        //	)
        //)
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        TupleSort unaryTupleSort = new TupleSort(translator.atomSort);
        
        BoundVariableDeclaration    sigVar  = new BoundVariableDeclaration(sigVarName, 
                                                    field.sig.type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstSigVar  = new BoundVariableDeclaration(fstSigVarName, 
                                                    fieldComponentExprs.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);  
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities

    }

    private void translateRelationOneMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
    {
        //(assert
        //	(forall ((x Atom))
        //		(=> (member (mkTuple x) Book)
        //			(exists ((y Atom))
        //				(and
        //					(member (mkTuple y) Addr)
        //					(member (mkTuple x y) addr)
        //					(forall ((z Atom))
        //						(=> (and 	(member (mkTuple z) Addr)
        //									(not (= z y)))
        //							(not (member (mkTuple x z) addr))
        //						)
        //					)
        //				)
        //			)
        //		)
        //	)
        //)
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();
        TupleSort unaryTupleSort = new TupleSort(translator.atomSort);
        
        BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, 
                                                            field.sig.type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstSigVar      = new BoundVariableDeclaration(fstSigVarName, 
                                                            fieldComponentExprs.get(0).type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstPrimeSigVar = new BoundVariableDeclaration(fstPrimeSigVarName, 
                                                            fieldComponentExprs.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());         
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression fstPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);       
        
        // forall a: Atom | a in fieldSigExpr => forall b : Atom | b in fstSigExpr => not (a, b) in fieldExpr
        
        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstPrimeSigVar.getConstantExpr(), fstSigVar.getConstantExpr()));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstPrimeSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), fstSigVar);
        
//        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerInnerExists), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));        

    }

    private void translateRelationLoneMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
    {
        //(assert
        //	(forall ((x Atom))
        //		(=> (member (mkTuple x) Book)
        //          or(
        //              (forall ((u Atom)) (=> (member (mkTuple u) Addr) (not (member (mkTuple x u) addr))))
        //			    (exists ((y Atom))
        //				    (and
        //					    (member (mkTuple y) Addr)
        //					    (member (mkTuple x y) addr)
        //					    (forall ((z Atom))
        //						    (=> (and 	(member (mkTuple z) Addr)
        //									    (not (= z y)))
        //							    (not (member (mkTuple x z) addr))
        //						    )
        //					    )
        //				    )
        //              )
        //			)
        //		)
        //	)
        //)
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();
        TupleSort unaryTupleSort = new TupleSort(translator.atomSort);
        
        BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, 
                                                            field.sig.type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstSigVar      = new BoundVariableDeclaration(fstSigVarName, 
                                                            fieldComponentExprs.get(0).type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstPrimeSigVar = new BoundVariableDeclaration(fstPrimeSigVarName, 
                                                            fieldComponentExprs.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getConstantExpr()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0), new HashMap<>());        
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression fstPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);       
        
        // forall a: Atom | a in fieldSigExpr => forall b : Atom | b in fstSigExpr => not (a, b) in fieldExpr
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, 
                                                                        new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), fstSigVar);        
        
        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstPrimeSigVar.getConstantExpr(), fstSigVar.getConstantExpr()));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstPrimeSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), fstSigVar);
        
//        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall)), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));
    }
    
    
    
    
    
    
    
    
    /**
     *
     *  Functions for translating nested multiplicities  
     *
     */
    
    

    // ANY_ARROW_SOME
    private void translateNestedAnyArrowSome(ExprBinary exprBinary, List<Sig> fieldSignatures, Sig.Field field)
    {   
        int numOfSigs   = fieldSignatures.size();
        int leftArity   = exprBinary.left.type().arity();
        int rightArity  = exprBinary.right.type().arity();
        
        if(numOfSigs == 2)
        {
            String sigVarName       = TranslatorUtils.getNewName();
            String fstSigVarName    = TranslatorUtils.getNewName();
            String sndSigVarName    = TranslatorUtils.getNewName();

            Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
            Sort fstSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
            Sort sndSigVarSort  = fieldSignatures.get(1).type().is_int()?translator.intSort:translator.atomSort;          

            BoundVariableDeclaration    sigVar  = new BoundVariableDeclaration(sigVarName, sigVarSort);
            BoundVariableDeclaration fstSigVar  = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
            BoundVariableDeclaration sndSigVar  = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);

            Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
            Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
            Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr(); 
            Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 

            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                                BinaryExpression.Op.MEMBER, sigExpr);
            Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, fstSigExpr); 
            Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, sndSigExpr);  
            Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                                BinaryExpression.Op.MEMBER, fieldExpr);        
            sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

            QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, sndSigVarMembership, sndSigVar);
            QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
            QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

            translator.smtProgram.addAssertion(new Assertion(outerForall));            
        }
        else
        {
            String sigVarName       = TranslatorUtils.getNewName();
            String fstSigVarName    = TranslatorUtils.getNewName();
            String sndSigVarName    = TranslatorUtils.getNewName();
            
            String leftSetName      = TranslatorUtils.getNewSetName();
            String rightSetName     = TranslatorUtils.getNewSetName();

            Sort                        sigVarSort  = field.sig.type().is_int()?translator.intSort:translator.atomSort;
            BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, sigVarSort);
            
            Sort fstSigVarSort;
            Sort sndSigVarSort;
            
            Expression leftSigExpr;
            Expression rightSigExpr;
            
            BoundVariableDeclaration fstSigVar;
            BoundVariableDeclaration sndSigVar;

            Expression fstSigVarMembership;
            Expression sndSigVarMembership;
            Expression fieldMembership;

            Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
            Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
            
            
            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                                BinaryExpression.Op.MEMBER, sigExpr);         
            Expression sigVarSet            = mkSinletonOutofAtoms(sigVar.getConstantExpr());
            
            if(leftArity > 1)
            {
                List<Sort> elementSorts = new ArrayList<>();
                
                for(int i = 0; i < leftArity && i < numOfSigs; ++i)
                {
                    Sort s  = fieldSignatures.get(i).type().is_int()?translator.intSort:translator.atomSort;
                    elementSorts.add(s);
                }
                fstSigVarSort = new TupleSort(elementSorts);
                FunctionDeclaration varDecl = new FunctionDeclaration(leftSetName, new SetSort(fstSigVarSort));                                
                leftSigExpr = varDecl.getConstantExpr();
                translator.smtProgram.addFcnDecl(varDecl);
                fstSigVar           = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);                
                fstSigVarMembership = new BinaryExpression(fstSigVar.getConstantExpr(),
                                                                BinaryExpression.Op.MEMBER, leftSigExpr);  
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(fstSigVar.getConstantExpr()));
                
                // Translate left expression
//                translateNestedMultiplicities();
            }
            else
            {
                leftSigExpr         = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
                fstSigVarSort       = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
                fstSigVar           = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
                fstSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, leftSigExpr);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(fstSigVar.getConstantExpr()));
            }
            
            if(rightArity > 1)
            {
                List<Sort> elementSorts = new ArrayList<>();
                
                for(int i = leftArity; i < leftArity+rightArity && i < numOfSigs; ++i)
                {
                    Sort s  = fieldSignatures.get(i).type().is_int()?translator.intSort:translator.atomSort;
                    elementSorts.add(s);
                }                
                sndSigVarSort = new TupleSort(elementSorts);   
                FunctionDeclaration varDecl = new FunctionDeclaration(rightSetName, new SetSort(sndSigVarSort));
                rightSigExpr = varDecl.getConstantExpr();
                sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
                sndSigVarMembership = new BinaryExpression(sndSigVar.getConstantExpr(),
                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
                translator.smtProgram.addFcnDecl(varDecl);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(sndSigVar.getConstantExpr()));
                // Translate right expression
//                translateNestedMultiplicities();                                
            }
            else
            {                
                rightSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();             
                sndSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
                sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
                sndSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(sndSigVar.getConstantExpr()));                
            }

            if(leftArity > 1 || rightArity > 1)
            {
                fieldMembership = new BinaryExpression(sigVarSet, BinaryExpression.Op.SUBSET, fieldExpr);                     
            }
            else
            {
                fieldMembership = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                                                BinaryExpression.Op.MEMBER, fieldExpr);                  
            }
           
            sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

            QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, sndSigVarMembership, sndSigVar);
            QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
            QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

            translator.smtProgram.addAssertion(new Assertion(outerForall));                 
        }
        //ToDo: handle nested multiplicities
    }
    
    // SOME_ARROW_ANY
    private void translateNestedSomeArrowAny(List<Sig> fieldSignatures, Sig.Field field)
    {   
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        
        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldSignatures.get(1).type().is_int()?translator.intSort:translator.atomSort;  
        
        BoundVariableDeclaration    sigVar  = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration sndSigVar  = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration fstSigVar  = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();    
        // Change the order of fst and snd sig expressions
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr(); 
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);  
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstSigVarMembership, fstSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sndSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }    
    
    // ONE_ARROW_ANY
    private void translateNestedOneArrowAny(List<Sig> fieldSignatures, Sig.Field field)
    {
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldSignatures.get(1).type().is_int()?translator.intSort:translator.atomSort;            
        
        BoundVariableDeclaration    sigVar          = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar          = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar          = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar     = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();        
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr(); 
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndSigVar.getConstantExpr(), fstSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr(), fstSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerForall), sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }                   
        
    // ANY_ARROW_ONE
    private void translateNestedAnyArrowOne(List<Sig> fieldSignatures, Sig.Field field)
    {
        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldSignatures.get(1).type().is_int()?translator.intSort:translator.atomSort;          
        
        BoundVariableDeclaration    sigVar          = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar          = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar          = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar     = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr(); 
        Expression fieldExpr    = translator.fieldsMap.get(field).getConstantExpr(); 
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getConstantExpr()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndSigVar.getConstantExpr()), 
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getConstantExpr(), sndSigVar.getConstantExpr()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getConstantExpr(), fstSigVar.getConstantExpr(), sndPrimeSigVar.getConstantExpr()),  
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));
        
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, innerInnerForall), sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        translator.smtProgram.addAssertion(new Assertion(outerForall));

        //ToDo: handle nested multiplicities
    }    
    
    public Expression mkTupleOutofAtoms(List<Expression> atomExprs)
    {
        if(atomExprs == null)
        {
            throw new RuntimeException();
        }
        else 
        {            
            return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        }        
    } 
    
    
    public Expression mkTupleOutofAtoms(Expression ... atomExprs)
    {
        if(atomExprs == null)
        {
            throw new RuntimeException();
        }
        else 
        {            
            return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        }        
    } 

    public Expression mkSinletonOutofAtoms(Expression ... atomExprs)
    {
        if(atomExprs == null)
        {
            throw new RuntimeException();
        }
        else 
        {            
            return new UnaryExpression(UnaryExpression.Op.SINGLETON, mkTupleOutofAtoms(atomExprs));
        }        
    }
    
    public Expression mkSinletonOutofAtoms(List<Expression> atomExprs)
    {
        if(atomExprs == null)
        {
            throw new RuntimeException();
        }
        else 
        {            
            return new UnaryExpression(UnaryExpression.Op.SINGLETON, mkTupleOutofAtoms(atomExprs));
        }        
    } 
    
    public Expression mkSinletonOutofTuple(Expression tupleExpr)
    {
        if(tupleExpr == null)
        {
            throw new RuntimeException();
        }
        else 
        {            
            return new UnaryExpression(UnaryExpression.Op.SINGLETON, tupleExpr);
        }        
    }  
    
    public boolean isArrowRelated(ExprBinary bExpr)
    {
        return (bExpr.op == ExprBinary.Op.ARROW) || (bExpr.op == ExprBinary.Op.ANY_ARROW_LONE) ||
               (bExpr.op == ExprBinary.Op.ANY_ARROW_ONE) || (bExpr.op == ExprBinary.Op.ANY_ARROW_SOME) ||
               (bExpr.op == ExprBinary.Op.SOME_ARROW_ANY) || (bExpr.op == ExprBinary.Op.SOME_ARROW_LONE) ||
               (bExpr.op == ExprBinary.Op.SOME_ARROW_ONE) || (bExpr.op == ExprBinary.Op.SOME_ARROW_SOME) ||
               (bExpr.op == ExprBinary.Op.LONE_ARROW_ANY) || (bExpr.op == ExprBinary.Op.LONE_ARROW_LONE) ||
               (bExpr.op == ExprBinary.Op.LONE_ARROW_ONE) || (bExpr.op == ExprBinary.Op.LONE_ARROW_SOME) ||
               (bExpr.op == ExprBinary.Op.ONE_ARROW_ANY) || (bExpr.op == ExprBinary.Op.ONE_ARROW_LONE) ||
               (bExpr.op == ExprBinary.Op.ONE_ARROW_ONE) || (bExpr.op == ExprBinary.Op.ONE_ARROW_SOME);
    }
}
