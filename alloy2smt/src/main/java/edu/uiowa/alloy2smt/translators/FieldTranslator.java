/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.smt.smtAst.*;
import java.util.ArrayList;
import java.util.List;

public class FieldTranslator
{

    private final Alloy2SmtTranslator translator;
    public  List<Sig.Field> fields = new ArrayList<>();

    public FieldTranslator(Alloy2SmtTranslator translator)
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
                collectFieldComponentExprs(((ExprBinary)((ExprUnary) expr).sub).left, fieldComponentExprs);
                collectFieldComponentExprs(((ExprBinary)((ExprUnary) expr).sub).right, fieldComponentExprs);     
            }            
            else
            {
                throw new UnsupportedOperationException("Something we have not supported yet: " + ((ExprUnary) expr).sub);
            }
        }
        else if(expr instanceof ExprBinary)
        {
            collectFieldComponentExprs(((ExprBinary)expr).left, fieldComponentExprs);
            collectFieldComponentExprs(((ExprBinary)expr).right, fieldComponentExprs);           
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
        Expression  first   = translator.signaturesMap.get(field.sig).getVariable();
        Expression  second  = (fieldComponentExprs.get(1) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));
        BinaryExpression    product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldComponentExprs.size(); i++)
        {       
            Expression  expr  = (fieldComponentExprs.get(i) instanceof Sig) ? 
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(i)).getVariable()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(i));
            product = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);            
        }
        // Collect field's type information
        for(int i = 0; i < fieldComponentExprs.size(); i++)
        {
            if(fieldComponentExprs.get(i).type().is_int())
            {
                fieldSorts.add(AbstractTranslator.uninterpretedInt);
            }
            else
            {
                fieldSorts.add(AbstractTranslator.atomSort);
            }
        }        
        
      
        FunctionDeclaration fieldDecl = new FunctionDeclaration(fieldName, new SetSort(new TupleSort(fieldSorts)));
        // declare a variable for the field
        translator.smtProgram.addFunction(fieldDecl);
        translator.fieldsMap.put(field, fieldDecl);
        // make a subset assertion
        translator.smtProgram.addAssertion(new Assertion(new BinaryExpression(fieldDecl.getVariable(), BinaryExpression.Op.SUBSET, product)));

        // translateExpr multiplicities and remove the first field Sig in fieldComponentExprs
        fieldComponentExprs.remove(0);
        translateMultiplicities(field, fieldComponentExprs, fieldSorts);
    }

    private void translateMultiplicities(Sig.Field field, List<Expr> fieldComponentExprs, List<Sort>  fieldSorts)
    {
        Expression multExpr = null;
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
                case SOMEOF     : multExpr = translateRelationSomeMultiplicity(field, fieldComponentExprs);break;
                case LONEOF     : multExpr = translateRelationLoneMultiplicity(field, fieldComponentExprs);break;
                case ONEOF      : multExpr = translateRelationOneMultiplicity(field, fieldComponentExprs);break;
                case SETOF      : multExpr = new BoolConstant(true);break; // no assertion needed
                case EXACTLYOF  : break; //ToDo: review translator case
                default:
                {
                    throw new UnsupportedOperationException("Not supported yet");
                }
            }
        }
        else if (expr instanceof ExprBinary)
        {
            multExpr = translateBinaryMultiplicities((ExprBinary) expr, field, fieldComponentExprs);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
        translator.smtProgram.addAssertion(new Assertion("Multiplicities constraint", multExpr));
    }


    private Expression translateBinaryMultiplicities(ExprBinary exprBinary, Sig.Field field, List<Expr> fieldComponentExprs)
    {
        if(fieldComponentExprs.size() > 2)
        {
            throw new UnsupportedOperationException("Currently, we do not support multiplicity constraints on relations with arity GT 3!");
        }

        Expression expr  = null;

        switch (exprBinary.op)
        {
            case ARROW              : expr = new BoolConstant(true);break;
            case ANY_ARROW_SOME     : expr = translateAnyArrowSome(fieldComponentExprs, field); break;
            case ANY_ARROW_ONE      : expr = translateAnyArrowOne(fieldComponentExprs, field); break;
            case ANY_ARROW_LONE     : expr = translateAnyArrowLone(fieldComponentExprs, field); break;
            case SOME_ARROW_ANY     : expr = translateSomeArrowAny(fieldComponentExprs, field); break;
            case SOME_ARROW_SOME    :
            {
                expr = new BinaryExpression(translateAnyArrowSome(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateSomeArrowAny(fieldComponentExprs, field)); break;
            }
            case SOME_ARROW_ONE     :
            {
                expr = new BinaryExpression(translateAnyArrowOne(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateSomeArrowAny(fieldComponentExprs, field)); break;
            }
            case SOME_ARROW_LONE    :
            {
                expr = new BinaryExpression(translateAnyArrowLone(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateSomeArrowAny(fieldComponentExprs, field)); break;
            }
            case ONE_ARROW_ANY      : expr = translateOneArrowAny(fieldComponentExprs, field); break;
            case ONE_ARROW_SOME     :
            {
                expr = new BinaryExpression(translateAnyArrowSome(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateOneArrowAny(fieldComponentExprs, field)); break;
            }
            case ONE_ARROW_ONE      :
            {
                expr = new BinaryExpression(translateOneArrowAny(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                             translateAnyArrowOne(fieldComponentExprs, field)); break;
            }
            case ONE_ARROW_LONE     :
            {
                expr = new BinaryExpression(translateOneArrowAny(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                             translateAnyArrowLone(fieldComponentExprs, field)); break;
            }
            case LONE_ARROW_ANY     : expr = translateLoneArrowAny(fieldComponentExprs, field); break;
            case LONE_ARROW_SOME    :
            {
                expr = new BinaryExpression(translateAnyArrowSome(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateLoneArrowAny(fieldComponentExprs, field)); break;
            }
            case LONE_ARROW_ONE     :
            {
                expr = new BinaryExpression(translateLoneArrowAny(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateAnyArrowOne(fieldComponentExprs, field)); break;
            }
            case LONE_ARROW_LONE    :
            {
                expr = new BinaryExpression(translateAnyArrowLone(fieldComponentExprs, field), BinaryExpression.Op.AND,
                                            translateLoneArrowAny(fieldComponentExprs, field)); break;
            }
            case ISSEQ_ARROW_LONE   : throw new UnsupportedOperationException();
            default:
            {
                throw new UnsupportedOperationException();
            }
        }
        return expr;
    }


    // ANY_ARROW_SOME
    private Expression translateAnyArrowSome(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar  = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar  = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar  = new VariableDeclaration(sndSigVarName, sndSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());

        Expression fstTupSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr, BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, sndSigVarMembership, sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;
        //ToDo: handle nested multiplicities
    }

    // SOME_ARROW_ANY
    private Expression translateSomeArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar  = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration sndSigVar  = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration fstSigVar  = new VariableDeclaration(fstSigVarName, fstSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());

        Expression fstTupSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        // Change the order of fst and snd sig expressions
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr,
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr,
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr,
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);
        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, fstSigVarMembership, fstSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sndSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;

        //ToDo: handle nested multiplicities
    }

    // ONE_ARROW_ANY
    private Expression translateOneArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration fstPrimeSigVar     = new VariableDeclaration(fstPrimeSigVarName, fstSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());
        Expression fstPrimeSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstPrimeSigVar.getVariable())
                                :mkTupleOutofAtoms(fstPrimeSigVar.getVariable());

        Expression fstTupSigVarExpr    = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);
        Expression fstTupFstPrimeSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstPrimeSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));

        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr, BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression fstPrimeSigVarMembership  = new BinaryExpression(fstPrimeSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);
//        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstPrimeSigVarExpr, fstSigVarExpr));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstPrimeSigVarExpr, fstTupSndSigVarExpr),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS,
                                                new BinaryExpression(new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership), BinaryExpression.Op.AND, innerInnerForall),
                                                fstSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sndSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;
        //ToDo: handle nested multiplicities
    }

    // ANY_ARROW_ONE
    private Expression translateAnyArrowOne(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration sndPrimeSigVar     = new VariableDeclaration(sndPrimeSigVarName, sndSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());
        Expression sndPrimeSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndPrimeSigVar.getVariable())
                                :mkTupleOutofAtoms(sndPrimeSigVar.getVariable());

        Expression fstTupSigVarExpr    = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);
        Expression fstTupSndPrimeSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndPrimeSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));

        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr, BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression sndPrimeSigVarMembership  = new BinaryExpression(sndPrimeSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);

        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVarExpr, sndSigVarExpr));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndPrimeSigVarExpr),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);

        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS,
                                                new BinaryExpression(new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership), BinaryExpression.Op.AND, innerInnerForall),
                                                sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;
        //ToDo: handle nested multiplicities
    }

    private Expression translateAnyArrowLone(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String sndPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration sndPrimeSigVar     = new VariableDeclaration(sndPrimeSigVarName, sndSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());
        Expression sndPrimeSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndPrimeSigVar.getVariable())
                                :mkTupleOutofAtoms(sndPrimeSigVar.getVariable());

        Expression fstTupSigVarExpr    = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);
        Expression fstTupSndPrimeSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndPrimeSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));

        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr, BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression sndPrimeSigVarMembership  = new BinaryExpression(sndPrimeSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);

        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVarExpr, sndSigVarExpr));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndPrimeSigVarExpr),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, sndPrimeSigVarMembership, sndPrimeSigVar);
        QuantifiedExpression innerOrForall  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), sndSigVar);
        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS,
                                                new BinaryExpression(new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership), BinaryExpression.Op.AND, innerInnerForall),
                                                sndSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerExists, BinaryExpression.Op.OR, innerOrForall)), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;
        //ToDo: handle nested multiplicities
    }

   private Expression translateLoneArrowAny(List<Expr> fieldComponentExprs, Sig.Field field)
    {
        boolean isSigVarInt = field.sig.type().is_int();
        boolean isFstSigVarInt = fieldComponentExprs.get(0).type().is_int();
        boolean isSndSigVarInt = fieldComponentExprs.get(1).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String sndSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();

        Sort sigVarSort     = isSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort fstSigVarSort  = isFstSigVarInt?translator.uninterpretedInt :translator.atomSort;
        Sort sndSigVarSort  = isSndSigVarInt?translator.uninterpretedInt :translator.atomSort;

        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration fstPrimeSigVar     = new VariableDeclaration(fstPrimeSigVarName, fstSigVarSort);

        Expression sigVarExpr = isSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable())
                                :mkTupleOutofAtoms(sigVar.getVariable());
        Expression fstSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable())
                                :mkTupleOutofAtoms(fstSigVar.getVariable());
        Expression sndSigVarExpr = isSndSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, sndSigVar.getVariable())
                                :mkTupleOutofAtoms(sndSigVar.getVariable());
        Expression fstPrimeSigVarExpr = isFstSigVarInt?new FunctionCallExpression(translator.uninterpretedIntValue, fstPrimeSigVar.getVariable())
                                :mkTupleOutofAtoms(fstPrimeSigVar.getVariable());

        Expression fstTupSigVarExpr    = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sigVarExpr);
        Expression fstTupFstSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstSigVarExpr);
        Expression fstTupSndSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, sndSigVarExpr);
        Expression fstTupFstPrimeSigVarExpr = new BinaryExpression(IntConstant.getInstance(0), BinaryExpression.Op.TUPSEL, fstPrimeSigVarExpr);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression sndSigExpr   = (fieldComponentExprs.get(1) instanceof Sig) ?
                                translator.signaturesMap.get((Sig)fieldComponentExprs.get(1)).getVariable()
                                : translator.exprTranslator.translateExpr(fieldComponentExprs.get(1));

        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(sigVarExpr, BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(fstSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(sndSigVarExpr, BinaryExpression.Op.MEMBER, sndSigExpr);
        Expression fstPrimeSigVarMembership  = new BinaryExpression(fstPrimeSigVarExpr, BinaryExpression.Op.MEMBER, fstSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstSigVarExpr, fstTupSndSigVarExpr),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);
//        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstPrimeSigVarExpr, fstSigVarExpr));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(fstTupSigVarExpr, fstTupFstPrimeSigVarExpr, fstTupSndSigVarExpr),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);

        QuantifiedExpression innerOrForall  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), fstSigVar);
        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS,
                                                new BinaryExpression(new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership), BinaryExpression.Op.AND, innerInnerForall),
                                                fstSigVar);
        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerExists, BinaryExpression.Op.OR, innerOrForall)), sndSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerForall), sigVar);

        return outerForall;

        //ToDo: handle nested multiplicities
    }


    private Expression translateRelationSomeMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
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

        Boolean sigVarIsInt     = field.sig.type().is_int();
        Boolean fstSigVarIsInt  = fieldComponentExprs.get(0).type().is_int();

        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        TupleSort unaryTupleSort = new TupleSort(translator.atomSort);

        VariableDeclaration sigVar  = new VariableDeclaration(sigVarName,
                                                    sigVarIsInt? translator.uninterpretedInt :translator.atomSort);
        VariableDeclaration fstSigVar  = new VariableDeclaration(fstSigVarName,
                                                    fstSigVarIsInt? translator.uninterpretedInt :translator.atomSort);

        Expression sigVarIntExpr    = translator.exprTranslator.exprBinaryTranslator.mkTupleSelectExpr(new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable()), 0);
        Expression fstSigVarIntExpr = translator.exprTranslator.exprBinaryTranslator.mkTupleSelectExpr(new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable()), 0);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVarIsInt?sigVarIntExpr:sigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVarIsInt?fstSigVarIntExpr:fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVarIsInt?sigVarIntExpr:sigVar.getVariable(), fstSigVarIsInt?fstSigVarIntExpr:fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);


        QuantifiedExpression innerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerExists), sigVar);

        return outerForall;

        //ToDo: handle nested multiplicities

    }

    private Expression translateRelationOneMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
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

        Boolean sigVarIsInt     = field.sig.type().is_int();
        Boolean fstSigVarIsInt  = fieldComponentExprs.get(0).type().is_int();


        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();

        VariableDeclaration sigVar      = new VariableDeclaration(sigVarName,
                                                    sigVarIsInt? translator.uninterpretedInt :translator.atomSort);
        VariableDeclaration fstSigVar      = new VariableDeclaration(fstSigVarName,
                                                    fstSigVarIsInt? translator.uninterpretedInt :translator.atomSort);
        VariableDeclaration fstPrimeSigVar = new VariableDeclaration(fstPrimeSigVarName,
                                                    fstSigVarIsInt? translator.uninterpretedInt :translator.atomSort);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMember = sigVar.getVariable();
        Expression fstSigVarMember = fstSigVar.getVariable();
        Expression fstPrimeSigVarMember = fstPrimeSigVar.getVariable();

        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVarMember),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression fstPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstPrimeSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVarMember, fstSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);

        // forall a: Atom | a in fieldSigExpr => forall b : Atom | b in fstSigExpr => not (a, b) in fieldExpr

        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstSigVarMember, fstPrimeSigVarMember));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVarMember, fstPrimeSigVarMember),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), fstSigVar);

        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, innerInnerExists), sigVar);

        return outerForall;

    }

    private Expression translateRelationLoneMultiplicity(Sig.Field field, List<Expr> fieldComponentExprs)
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
        Boolean sigVarIsInt     = field.sig.type().is_int();
        Boolean fstSigVarIsInt  = fieldComponentExprs.get(0).type().is_int();


        String sigVarName       = TranslatorUtils.getNewName();
        String fstSigVarName    = TranslatorUtils.getNewName();
        String fstPrimeSigVarName    = TranslatorUtils.getNewName();
        TupleSort unaryTupleSort = new TupleSort(translator.atomSort);

        VariableDeclaration sigVar      = new VariableDeclaration(sigVarName,
                                                    sigVarIsInt? translator.uninterpretedInt :translator.atomSort);
        VariableDeclaration fstSigVar      = new VariableDeclaration(fstSigVarName,
                                                    fstSigVarIsInt? translator.uninterpretedInt :translator.atomSort);
        VariableDeclaration fstPrimeSigVar = new VariableDeclaration(fstPrimeSigVarName,
                                                    fstSigVarIsInt? translator.uninterpretedInt :translator.atomSort);

        Expression sigVarIntExpr    = translator.exprTranslator.exprBinaryTranslator.mkTupleSelectExpr(new FunctionCallExpression(translator.uninterpretedIntValue, sigVar.getVariable()), 0);
        Expression fstSigVarIntExpr = translator.exprTranslator.exprBinaryTranslator.mkTupleSelectExpr(new FunctionCallExpression(translator.uninterpretedIntValue, fstSigVar.getVariable()), 0);
        Expression fstPrimeSigVarIntExpr = translator.exprTranslator.exprBinaryTranslator.mkTupleSelectExpr(new FunctionCallExpression(translator.uninterpretedIntValue, fstPrimeSigVar.getVariable()), 0);

        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = (fieldComponentExprs.get(0) instanceof Sig) ?
                                    translator.signaturesMap.get((Sig)fieldComponentExprs.get(0)).getVariable()
                                    : translator.exprTranslator.translateExpr(fieldComponentExprs.get(0));
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

        Expression sigVarMember = sigVarIsInt?sigVarIntExpr:sigVar.getVariable();
        Expression fstSigVarMember = fstSigVarIsInt?fstSigVarIntExpr:fstSigVar.getVariable();
        Expression fstPrimeSigVarMember = fstSigVarIsInt?fstPrimeSigVarIntExpr:fstPrimeSigVar.getVariable();

        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVarMember),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);
        Expression fstPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstPrimeSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);

        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVarMember, fstSigVarMember),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);

        // forall a: Atom | a in fieldSigExpr => forall b : Atom | b in fstSigExpr => not (a, b) in fieldExpr

        fstSigVarMembership = new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, fieldMembership);

        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(fstSigVarMember, fstPrimeSigVarMember));
        fstPrimeSigVarMembership = new BinaryExpression(fstPrimeSigVarMembership, BinaryExpression.Op.IMPLIES,
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVarMember, fstPrimeSigVarMember),
                                                                                                                        BinaryExpression.Op.MEMBER, fieldExpr)));

        QuantifiedExpression innerInnerExistsForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, fstPrimeSigVarMembership, fstPrimeSigVar);
        QuantifiedExpression innerInnerExists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.AND, innerInnerExistsForall), fstSigVar);

        // forall a: Atom | a in fieldSigExpr => forall b : Atom | b in fstSigExpr => not (a, b) in fieldExpr
        QuantifiedExpression innerInnerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL,
                                                                        new BinaryExpression(fstSigVarMembership, BinaryExpression.Op.IMPLIES, new UnaryExpression(UnaryExpression.Op.NOT, fieldMembership)), fstSigVar);

//        QuantifiedExpression innerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall), fstSigVar);
        QuantifiedExpression outerForall = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new BinaryExpression(sigVarMembership, BinaryExpression.Op.IMPLIES, new BinaryExpression(innerInnerExists, BinaryExpression.Op.OR, innerInnerForall)), sigVar);

        return outerForall;
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

            VariableDeclaration sigVar  = new VariableDeclaration(sigVarName, sigVarSort);
            VariableDeclaration fstSigVar  = new VariableDeclaration(fstSigVarName, fstSigVarSort);
            VariableDeclaration sndSigVar  = new VariableDeclaration(sndSigVarName, sndSigVarSort);

            Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
            Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getVariable();
            Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getVariable();
            Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();

            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, sigExpr);
            Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, fstSigExpr);
            Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, sndSigExpr);
            Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), fstSigVar.getVariable(), sndSigVar.getVariable()),
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
            VariableDeclaration sigVar      = new VariableDeclaration(sigVarName, sigVarSort);

            Sort fstSigVarSort;
            Sort sndSigVarSort;

            Expression leftSigExpr;
            Expression rightSigExpr;

            VariableDeclaration fstSigVar;
            VariableDeclaration sndSigVar;

            Expression fstSigVarMembership;
            Expression sndSigVarMembership;
            Expression fieldMembership;

            Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
            Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();


            Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, sigExpr);
            Expression sigVarSet            = mkSinletonOutofAtoms(sigVar.getVariable());

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
                leftSigExpr = varDecl.getVariable();
                translator.smtProgram.addFunction(varDecl);
                fstSigVar           = new VariableDeclaration(fstSigVarName, fstSigVarSort);
                fstSigVarMembership = new BinaryExpression(fstSigVar.getVariable(),
                                                                BinaryExpression.Op.MEMBER, leftSigExpr);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(fstSigVar.getVariable()));

                // Translate left expression
//                translateNestedMultiplicities();
            }
            else
            {
                leftSigExpr         = translator.signaturesMap.get(fieldSignatures.get(0)).getVariable();
                fstSigVarSort       = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
                fstSigVar           = new VariableDeclaration(fstSigVarName, fstSigVarSort);
                fstSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, leftSigExpr);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(fstSigVar.getVariable()));
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
                rightSigExpr = varDecl.getVariable();
                sndSigVar      = new VariableDeclaration(sndSigVarName, sndSigVarSort);
                sndSigVarMembership = new BinaryExpression(sndSigVar.getVariable(),
                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
                translator.smtProgram.addFunction(varDecl);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofTuple(sndSigVar.getVariable()));
                // Translate right expression
//                translateNestedMultiplicities();                                
            }
            else
            {                
                rightSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getVariable();
                sndSigVarSort  = fieldSignatures.get(0).type().is_int()?translator.intSort:translator.atomSort;
                sndSigVar      = new VariableDeclaration(sndSigVarName, sndSigVarSort);
                sndSigVarMembership = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getVariable()),
                                                                BinaryExpression.Op.MEMBER, rightSigExpr);
                sigVarSet = new BinaryExpression(sigVarSet, BinaryExpression.Op.PRODUCT, mkSinletonOutofAtoms(sndSigVar.getVariable()));
            }

            if(leftArity > 1 || rightArity > 1)
            {
                fieldMembership = new BinaryExpression(sigVarSet, BinaryExpression.Op.SUBSET, fieldExpr);                     
            }
            else
            {
                fieldMembership = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), fstSigVar.getVariable(), sndSigVar.getVariable()),
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
        
        VariableDeclaration sigVar  = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration sndSigVar  = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration fstSigVar  = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        // Change the order of fst and snd sig expressions
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getVariable();
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getVariable();
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr);  
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), fstSigVar.getVariable(), sndSigVar.getVariable()),
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
        
        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration sndPrimeSigVar     = new VariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getVariable();
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getVariable();
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), sndSigVar.getVariable(), fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getVariable(), sndSigVar.getVariable()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), sndPrimeSigVar.getVariable(), fstSigVar.getVariable()),
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
        
        VariableDeclaration sigVar          = new VariableDeclaration(sigVarName, sigVarSort);
        VariableDeclaration fstSigVar          = new VariableDeclaration(fstSigVarName, fstSigVarSort);
        VariableDeclaration sndSigVar          = new VariableDeclaration(sndSigVarName, sndSigVarSort);
        VariableDeclaration sndPrimeSigVar     = new VariableDeclaration(sndPrimeSigVarName, sndSigVarSort);
        
        Expression sigExpr      = translator.signaturesMap.get(field.sig).getVariable();
        Expression fstSigExpr   = translator.signaturesMap.get(fieldSignatures.get(0)).getVariable();
        Expression sndSigExpr   = translator.signaturesMap.get(fieldSignatures.get(1)).getVariable();
        Expression fieldExpr    = translator.fieldsMap.get(field).getVariable();
                
        Expression sigVarMembership     = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sigExpr);
        Expression fstSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(fstSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fstSigExpr); 
        Expression sndSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr); 
        Expression sndPrimeSigVarMembership  = new BinaryExpression(mkTupleOutofAtoms(sndPrimeSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, sndSigExpr);         
        
        Expression fieldMembership      = new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), fstSigVar.getVariable(), sndSigVar.getVariable()),
                                                            BinaryExpression.Op.MEMBER, fieldExpr);        
        sndSigVarMembership = new BinaryExpression(sndSigVarMembership, BinaryExpression.Op.AND, fieldMembership);
        
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.AND, TranslatorUtils.mkDistinctExpr(sndPrimeSigVar.getVariable(), sndSigVar.getVariable()));
        sndPrimeSigVarMembership = new BinaryExpression(sndPrimeSigVarMembership, BinaryExpression.Op.IMPLIES, 
                                                        new UnaryExpression(UnaryExpression.Op.NOT, new BinaryExpression(mkTupleOutofAtoms(sigVar.getVariable(), fstSigVar.getVariable(), sndPrimeSigVar.getVariable()),
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
            List<Expression> exprs = new ArrayList<>();
            
            for(int i = 0; i < atomExprs.size(); ++i)
            {
                if(atomExprs.get(i) instanceof MultiArityExpression)
                {
                    if(((MultiArityExpression)atomExprs.get(i)).getOp() == MultiArityExpression.Op.MKTUPLE)
                    {
                        
                        exprs.addAll(((MultiArityExpression)atomExprs.get(i)).getExpressions());
                    }
                    else
                    {
                        throw new RuntimeException("Something is wrong here!");
                    }
                }
                else
                {
                    exprs.add(atomExprs.get(i));
                }
            }
            return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
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
            List<Expression> exprs = new ArrayList<>();
            
            for(int i = 0; i < atomExprs.length; ++i)
            {
                if(atomExprs[i] instanceof MultiArityExpression)
                {
                    if(((MultiArityExpression)atomExprs[i]).getOp() == MultiArityExpression.Op.MKTUPLE)
                    {
                        
                        exprs.addAll(((MultiArityExpression)atomExprs[i]).getExpressions());
                    }
                    else
                    {
                        throw new RuntimeException("Something is wrong here!");
                    }
                }
                else
                {
                    exprs.add(atomExprs[i]);
                }
            }
            return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, exprs);
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
