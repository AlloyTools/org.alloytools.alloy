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
import java.util.List;

public class FieldTranslator
{

    private final Alloy2SMTTranslator translator;
    public List<Sig.Field> fields = new ArrayList<>();

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
    
    void collectFieldSigs(Expr expr, List<Sig> fieldComponentTypes)
    {
        if(expr instanceof ExprUnary)
        {            
            if(((ExprUnary) expr).sub instanceof Sig)
            {
                fieldComponentTypes.add((Sig)((ExprUnary) expr).sub);
            }
            else if(((ExprUnary) expr).sub instanceof Sig.Field)
            {
                collectFieldSigs(((Sig.Field)((ExprUnary) expr).sub).decl().expr, fieldComponentTypes);
            }
            else if(((ExprUnary) expr).sub instanceof ExprUnary)
            {
                collectFieldSigs((ExprUnary)(((ExprUnary) expr).sub), fieldComponentTypes);
            }
            else if(((ExprUnary) expr).sub instanceof ExprVar)
            {
                //skip, ((ExprUnary) expr).sub = this
            }   
            else if(((ExprUnary) expr).sub instanceof ExprBinary)
            {
                collectFieldSigs(((ExprBinary)((ExprUnary) expr).sub).left, fieldComponentTypes);
                collectFieldSigs(((ExprBinary)((ExprUnary) expr).sub).right, fieldComponentTypes);
            }            
            else
            {
                throw new UnsupportedOperationException("Something we have not supported yet: " + ((ExprUnary) expr).sub);
            }
        }
        else if(expr instanceof ExprBinary)
        {
            collectFieldSigs(((ExprBinary)expr).left, fieldComponentTypes);
            collectFieldSigs(((ExprBinary)expr).right, fieldComponentTypes);
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

        // a field relation is a subset of the product of its signatures        
        List<Sig> fieldSignatures = new ArrayList<>();
        fieldSignatures.add(field.sig);
        collectFieldSigs(field.decl().expr, fieldSignatures);
        
        /* alloy: sig Book{addr: Name -> lone Addr}
         *  smt  : (assert (subset addr (product (product Book Name) Addr)))
         */
        ConstantExpression first   = translator.signaturesMap.get(field.sig).getConstantExpr();
        //ToDo: review the case when the relation uses a subset signature instead of a top level signature
        ConstantExpression second  = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();
        BinaryExpression product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldSignatures.size(); i++)
        {       
            product = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, translator.signaturesMap.get(fieldSignatures.get(i)).getConstantExpr());            
        }
        // Collect field's type information
        for(int i = 0; i < fieldSignatures.size(); i++)
        {
            if(fieldSignatures.get(i).type().is_int())
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
        // translateExpr multiplicities
        translateMultiplicities(field, fieldDecl);
    }

    private void translateMultiplicities(Sig.Field field, FunctionDeclaration declaration)
    {
        Expr expr = field.decl().expr;
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary) expr;
            
            List<Sig> fieldSignatures = new ArrayList<>();        

            collectFieldSigs(exprUnary, fieldSignatures);

            if(fieldSignatures.size() > 1)
            {
                throw new UnsupportedOperationException("We currenty do not support multiplicity constraints on nested relations!");
            }             
            switch (exprUnary.op)
            {
                case SOMEOF     : translateRelationSomeMultiplicity(field, declaration, fieldSignatures);break;
                case LONEOF     : translateRelationLoneMultiplicity(field, declaration, fieldSignatures);break;
                case ONEOF      : translateRelationOneMultiplicity(field, declaration, fieldSignatures);break;
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
            translateBinaryMultiplicities((ExprBinary) expr, field, declaration);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateBinaryMultiplicities(ExprBinary exprBinary, Sig.Field field, FunctionDeclaration declaration)
    {
        List<Sig> fieldSignatures = new ArrayList<>();        
        
        collectFieldSigs(field.decl().expr, fieldSignatures);
        
        if(fieldSignatures.size() > 2)
        {
            throw new UnsupportedOperationException("Does not support multiplicity constraints on relations with arity GT 3!");
        }        
        switch (exprBinary.op)
        {
            case ARROW              : break; // no assertion needed
            case ANY_ARROW_SOME     : translateAnyArrowSome(fieldSignatures, field, declaration); break;
            case ANY_ARROW_ONE      : translateAnyArrowOne(fieldSignatures, field, declaration); break;
            case ANY_ARROW_LONE     : translateAnyArrowLone(fieldSignatures, field, declaration); break;
            case SOME_ARROW_ANY     : translateSomeArrowAny(fieldSignatures, field, declaration); break;
            case SOME_ARROW_SOME    : 
            {
                translateAnyArrowSome(fieldSignatures, field, declaration);
                translateSomeArrowAny(fieldSignatures, field, declaration); break;
            }
            case SOME_ARROW_ONE     : 
            {
                translateAnyArrowOne(fieldSignatures, field, declaration); 
                translateSomeArrowAny(fieldSignatures, field, declaration); break;
            }
            case SOME_ARROW_LONE    : 
            {
                translateAnyArrowLone(fieldSignatures, field, declaration);
                translateSomeArrowAny(fieldSignatures, field, declaration); break;
            }
            case ONE_ARROW_ANY      : translateOneArrowAny(fieldSignatures, field, declaration); break;
            case ONE_ARROW_SOME     : 
            {
                translateAnyArrowSome(fieldSignatures, field, declaration);
                translateOneArrowAny(fieldSignatures, field, declaration); break;
            }
            case ONE_ARROW_ONE      : 
            {
                translateOneArrowAny(fieldSignatures, field, declaration); 
                translateAnyArrowOne(fieldSignatures, field, declaration); break;
            }
            case ONE_ARROW_LONE     : 
            {
                translateOneArrowAny(fieldSignatures, field, declaration); 
                translateAnyArrowLone(fieldSignatures, field, declaration); break;
            }
            case LONE_ARROW_ANY     : translateLoneArrowAny(fieldSignatures, field, declaration); break;
            case LONE_ARROW_SOME    : 
            {
                translateAnyArrowSome(fieldSignatures, field, declaration);
                translateLoneArrowAny(fieldSignatures, field, declaration); break;
            }
            case LONE_ARROW_ONE     : 
            {
                translateLoneArrowAny(fieldSignatures, field, declaration); 
                translateAnyArrowOne(fieldSignatures, field, declaration); break;
            }
            case LONE_ARROW_LONE    : 
            {
                translateAnyArrowLone(fieldSignatures, field, declaration); 
                translateLoneArrowAny(fieldSignatures, field, declaration); break;
            }
            case ISSEQ_ARROW_LONE   : throw new UnsupportedOperationException();
            default:
            {
                throw new UnsupportedOperationException();
            }
        }
    }

    // ANY_ARROW_SOME
    private void translateAnyArrowSome(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
    {   
        int numOfSigs           = fieldSignatures.size();
        
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
            
        }
        //ToDo: handle nested multiplicities
    }
    
    // SOME_ARROW_ANY
    private void translateSomeArrowAny(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
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
    private void translateOneArrowAny(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
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
    private void translateAnyArrowOne(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
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
    
    private void translateAnyArrowLone(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
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
    
   private void translateLoneArrowAny(List<Sig> fieldSignatures, Sig.Field field, FunctionDeclaration declaration)
    {
        String sigVarName           = TranslatorUtils.getNewName();
        String fstSigVarName        = TranslatorUtils.getNewName();
        String sndSigVarName        = TranslatorUtils.getNewName();
        String sndPrimeSigVarName   = TranslatorUtils.getNewName();
        Sort sigVarSort     = field.sig.type().is_int()?translator.intSort:translator.atomSort;
        Sort fstSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
        Sort sndSigVarSort  = fieldSignatures.get(1).type().is_int()?translator.intSort:translator.atomSort;
        
        BoundVariableDeclaration    sigVar      = new BoundVariableDeclaration(sigVarName, sigVarSort);
        BoundVariableDeclaration fstSigVar      = new BoundVariableDeclaration(fstSigVarName, fstSigVarSort);
        BoundVariableDeclaration sndSigVar      = new BoundVariableDeclaration(sndSigVarName, sndSigVarSort);
        BoundVariableDeclaration sndPrimeSigVar = new BoundVariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
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
    

    private void translateRelationSomeMultiplicity(Sig.Field field, FunctionDeclaration declaration, List<Sig> fieldSignatures)
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
                                                    fieldSignatures.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
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

    private void translateRelationOneMultiplicity(Sig.Field field, FunctionDeclaration declaration, List<Sig> fieldSignatures)
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
                                                            fieldSignatures.get(0).type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstPrimeSigVar = new BoundVariableDeclaration(fstPrimeSigVarName, 
                                                            fieldSignatures.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
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

    private void translateRelationLoneMultiplicity(Sig.Field field, FunctionDeclaration declaration, List<Sig> fieldSignatures)
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
                                                            fieldSignatures.get(0).type().is_int()? translator.intSort:translator.atomSort);
        BoundVariableDeclaration fstPrimeSigVar = new BoundVariableDeclaration(fstPrimeSigVarName, 
                                                            fieldSignatures.get(0).type().is_int()? translator.intSort:translator.atomSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getConstantExpr();        
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();        
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
}
