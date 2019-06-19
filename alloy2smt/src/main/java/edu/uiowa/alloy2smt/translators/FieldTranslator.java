/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
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
            ExprBinary exprBinary = (ExprBinary) expr;
            switch (exprBinary.op)
            {
                case ARROW              :
                case ANY_ARROW_SOME     :
                case ANY_ARROW_ONE      :
                case ANY_ARROW_LONE     :
                case SOME_ARROW_ANY     :
                case SOME_ARROW_SOME    :
                case SOME_ARROW_ONE     :
                case SOME_ARROW_LONE    :
                case ONE_ARROW_ANY      :
                case ONE_ARROW_SOME     :
                case ONE_ARROW_ONE      :
                case ONE_ARROW_LONE     :
                case LONE_ARROW_ANY     :
                case LONE_ARROW_SOME    :
                case LONE_ARROW_ONE     :
                case LONE_ARROW_LONE    :
                case ISSEQ_ARROW_LONE   :
                {
                    collectFieldComponentExprs(((ExprBinary) expr).left, fieldComponentExprs);
                    collectFieldComponentExprs(((ExprBinary) expr).right, fieldComponentExprs);
                    break;
                }
                case JOIN               :
                case DOMAIN             :
                case RANGE              :
                case INTERSECT          :
                case PLUSPLUS           :
                case PLUS               :
                case MINUS              :
                {
                    fieldComponentExprs.add(exprBinary);
                    break;
                }
                default                 : throw new UnsupportedOperationException();
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

        for (Sig sig : field.type().fold().get(0))
        {
            if(sig.type().is_int())
            {
                fieldSorts.add(AbstractTranslator.uninterpretedInt);
            }
            else
            {
                fieldSorts.add(AbstractTranslator.atomSort);
            }
        }

        FunctionDeclaration fieldDeclaration = new FunctionDeclaration(fieldName, new SetSort(new TupleSort(fieldSorts)));
        // declare a variable for the field
        translator.smtProgram.addFunction(fieldDeclaration);
        translator.fieldsMap.put(field, fieldDeclaration);
        translateMultiplicities(field);
    }

    private void translateMultiplicities(Sig.Field field)
    {
        // sig signature {field : expr}
        // all s: signature | s.field in expr
        Expr expr = field.decl().expr;
        ExprVar s = ExprVar.make(null, "_s", field.sig.type());
        Expr noopS = ExprUnary.Op.NOOP.make(null, s);
        Expr noopField = ExprUnary.Op.NOOP.make(null, field);
        Expr join = ExprBinary.Op.JOIN.make(null, null, noopS, noopField);
        Expr in = ExprBinary.Op.IN.make(null, null, join, expr);
        Expr noopSig = ExprUnary.Op.NOOP.make(null, field.sig);
        Decl decl = new Decl(null, null, null, Collections.singletonList(s), noopSig);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), in);
        Expression multiplicity =  translator.exprTranslator.translateExpr(exprQt);
        translator.smtProgram.addAssertion(new Assertion(field.toString() + " multiplicity", multiplicity));
        Expr product = ExprBinary.Op.ARROW.make(null, null, noopSig, expr);
        Expr subsetExpr = ExprBinary.Op.IN.make(null, null, noopField, product);
        Expression subsetExpression = translator.exprTranslator.translateExpr(subsetExpr);
        translator.smtProgram.addAssertion(new Assertion(field.toString() + " subset", subsetExpression));
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
