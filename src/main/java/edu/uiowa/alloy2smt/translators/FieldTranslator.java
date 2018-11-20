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
import java.util.stream.Collectors;
import java.util.stream.IntStream;

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
            if(translator.signatureTranslator.getAncestorSig(fieldSignatures.get(i)) == Sig.SIGINT)
            {
                fieldSorts.add(translator.intSort);
            }
            else
            {
                fieldSorts.add(translator.atomSort);
            }
        }        
        
      
        FunctionDeclaration declaration = new FunctionDeclaration(fieldName, new SetSort(new TupleSort(fieldSorts)));
        // declare a variable for the field
        translator.smtProgram.addFunctionDeclaration(declaration);
        translator.fieldsMap.put(field, declaration);   
        // make a subset assertion
        translator.smtProgram.addAssertion(new Assertion(new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.SUBSET, product)));
        // translateExpr multiplicities
        translateMultiplicities(field, declaration);
    }

    private void translateMultiplicities(Sig.Field field, FunctionDeclaration declaration)
    {
        Expr expr = field.decl().expr;
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary) expr;
            switch (exprUnary.op)
            {
                case SOMEOF     : translateRelationSomeMultiplicity(field, declaration, exprUnary);break;
                case LONEOF     : translateRelationLoneMultiplicity(field, declaration, exprUnary);break;
                case ONEOF      : translateRelationOneMultiplicity(field, declaration, exprUnary);break;
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
        switch (exprBinary.op)
        {
            case ARROW              : break; // no assertion needed
            case ANY_ARROW_SOME     : translateAnyArrowSome(exprBinary, field, declaration); break;
            case ANY_ARROW_ONE      : translateAnyArrowOne(exprBinary, field, declaration); break;
            case ANY_ARROW_LONE     : translateAnyArrowLone(exprBinary, field, declaration); break;
            case SOME_ARROW_ANY     : throw new UnsupportedOperationException();
            case SOME_ARROW_SOME    : throw new UnsupportedOperationException();
            case SOME_ARROW_ONE     : throw new UnsupportedOperationException();
            case SOME_ARROW_LONE    : throw new UnsupportedOperationException();
            case ONE_ARROW_ANY      : throw new UnsupportedOperationException();
            case ONE_ARROW_SOME     : throw new UnsupportedOperationException();
            case ONE_ARROW_ONE      : throw new UnsupportedOperationException();
            case ONE_ARROW_LONE     : throw new UnsupportedOperationException();
            case LONE_ARROW_ANY     : throw new UnsupportedOperationException();
            case LONE_ARROW_SOME    : throw new UnsupportedOperationException();
            case LONE_ARROW_ONE     : throw new UnsupportedOperationException();
            case LONE_ARROW_LONE    : throw new UnsupportedOperationException();
            case ISSEQ_ARROW_LONE   : throw new UnsupportedOperationException();
            default:
            {
                throw new UnsupportedOperationException();
            }
        }
    }

    private void translateAnyArrowSome(ExprBinary exprBinary, Sig.Field field, FunctionDeclaration declaration)
    {
        TupleSort tupleSort = new TupleSort(translator.atomSort);

        BoundVariableDeclaration sigVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort);

        List<Sig.PrimSig> leftSignatures = exprBinary.left.type().fold().get(0);

        List<BoundVariableDeclaration> leftVariables = IntStream
                .range(1, leftSignatures.size() + 1).boxed()
                .map(x -> new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort))
                .collect(Collectors.toList());

        Expression leftMembers = new BinaryExpression(leftVariables.get(0).getConstantExpr(),
                BinaryExpression.Op.MEMBER,
                translator.signaturesMap.get(leftSignatures.get(0)).getConstantExpr());

        for (int i = 1; i < leftSignatures.size(); i++)
        {
            Expression member = new BinaryExpression(leftVariables.get(i).getConstantExpr(),
                    BinaryExpression.Op.MEMBER,
                    translator.signaturesMap.get(leftSignatures.get(i)).getConstantExpr());
            leftMembers = new BinaryExpression(leftMembers, BinaryExpression.Op.AND, member);
        }

        UnaryExpression  singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, sigVariable.getConstantExpr());
        
        int rightArity = exprBinary.right.type().arity();

        Sort rightSort = new TupleSort(IntStream.range(1, rightArity + 1).boxed().map(x -> translator.atomSort).collect(Collectors.toList()));

        BoundVariableDeclaration rightVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), rightSort);

        Expression join = new BinaryExpression(singleton, BinaryExpression.Op.JOIN,  declaration.getConstantExpr());

        UnaryExpression unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(0).getConstantExpr());

        join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);

        for(int i = 1; i < leftVariables.size(); i++)
        {
            unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(i).getConstantExpr());

            join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);
        }

        BinaryExpression rightMember = new BinaryExpression(rightVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, join);

        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rightMember, rightVariable);

        BinaryExpression innerImplies = new BinaryExpression(leftMembers, BinaryExpression.Op.IMPLIES, exists);

        QuantifiedExpression innerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, leftVariables, innerImplies);

        Expression    sigExpression = translator.signaturesMap.get(field.sig).getConstantExpr();

        BinaryExpression member = new BinaryExpression(sigVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, sigExpression);

        BinaryExpression outerImplies = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, innerForAll);

        QuantifiedExpression outerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, outerImplies, sigVariable);

        translator.smtProgram.addAssertion(new Assertion(outerForAll));

        //ToDo: handle nested multiplicities
    }
    
    private void translateAnyArrowOne(ExprBinary exprBinary, Sig.Field field, FunctionDeclaration declaration)
    {
        TupleSort tupleSort = new TupleSort(translator.atomSort);

        BoundVariableDeclaration sigVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort);

        List<Sig.PrimSig> leftSignatures = exprBinary.left.type().fold().get(0);

        List<BoundVariableDeclaration> leftVariables = IntStream
                .range(1, leftSignatures.size() + 1).boxed()
                .map(x -> new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort))
                .collect(Collectors.toList());

        Expression leftMembers = new BinaryExpression(leftVariables.get(0).getConstantExpr(),
                BinaryExpression.Op.MEMBER,
                translator.signaturesMap.get(leftSignatures.get(0)).getConstantExpr());

        for (int i = 1; i < leftSignatures.size(); i++)
        {
            Expression member = new BinaryExpression(leftVariables.get(i).getConstantExpr(),
                    BinaryExpression.Op.MEMBER,
                    translator.signaturesMap.get(leftSignatures.get(i)).getConstantExpr());
            leftMembers = new BinaryExpression(leftMembers, BinaryExpression.Op.AND, member);
        }

        UnaryExpression  singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, sigVariable.getConstantExpr());
        
        int rightArity = exprBinary.right.type().arity();

        Sort rightSort = new TupleSort(IntStream.range(1, rightArity + 1).boxed().map(x -> translator.atomSort).collect(Collectors.toList()));

        BoundVariableDeclaration rightVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), rightSort);

        Expression join = new BinaryExpression(singleton, BinaryExpression.Op.JOIN,  declaration.getConstantExpr());

        UnaryExpression unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(0).getConstantExpr());

        join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);

        for(int i = 1; i < leftVariables.size(); i++)
        {
            unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(i).getConstantExpr());

            join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);
        }

        BinaryExpression rightMember = new BinaryExpression(rightVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, join);

        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rightMember, rightVariable);

        BinaryExpression innerImplies = new BinaryExpression(leftMembers, BinaryExpression.Op.IMPLIES, exists);

        QuantifiedExpression innerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, leftVariables, innerImplies);

        Expression    sigExpression = translator.signaturesMap.get(field.sig).getConstantExpr();

        BinaryExpression member = new BinaryExpression(sigVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, sigExpression);

        BinaryExpression outerImplies = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, innerForAll);

        QuantifiedExpression outerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, outerImplies, sigVariable);

        translator.smtProgram.addAssertion(new Assertion(outerForAll));

        //ToDo: handle nested multiplicities
    }    
    
    private void translateAnyArrowLone(ExprBinary exprBinary, Sig.Field field, FunctionDeclaration declaration)
    {
        TupleSort tupleSort = new TupleSort(translator.atomSort);

        BoundVariableDeclaration sigVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort);

        List<Sig.PrimSig> leftSignatures = exprBinary.left.type().fold().get(0);

        List<BoundVariableDeclaration> leftVariables = IntStream
                .range(1, leftSignatures.size() + 1).boxed()
                .map(x -> new BoundVariableDeclaration(TranslatorUtils.getNewName(), tupleSort))
                .collect(Collectors.toList());

        Expression leftMembers = new BinaryExpression(leftVariables.get(0).getConstantExpr(),
                BinaryExpression.Op.MEMBER,
                translator.signaturesMap.get(leftSignatures.get(0)).getConstantExpr());

        for (int i = 1; i < leftSignatures.size(); i++)
        {
            Expression member = new BinaryExpression(leftVariables.get(i).getConstantExpr(),
                    BinaryExpression.Op.MEMBER,
                    translator.signaturesMap.get(leftSignatures.get(i)).getConstantExpr());
            leftMembers = new BinaryExpression(leftMembers, BinaryExpression.Op.AND, member);
        }

        UnaryExpression  singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, sigVariable.getConstantExpr());
        
        int rightArity = exprBinary.right.type().arity();

        Sort rightSort = new TupleSort(IntStream.range(1, rightArity + 1).boxed().map(x -> translator.atomSort).collect(Collectors.toList()));

        BoundVariableDeclaration rightVariable = new BoundVariableDeclaration(TranslatorUtils.getNewName(), rightSort);

        Expression join = new BinaryExpression(singleton, BinaryExpression.Op.JOIN,  declaration.getConstantExpr());

        UnaryExpression unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(0).getConstantExpr());

        join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);

        for(int i = 1; i < leftVariables.size(); i++)
        {
            unary = new UnaryExpression(UnaryExpression.Op.SINGLETON, leftVariables.get(i).getConstantExpr());

            join = new BinaryExpression(unary, BinaryExpression.Op.JOIN, join);
        }

        BinaryExpression rightMember = new BinaryExpression(rightVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, join);

        QuantifiedExpression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, rightMember, rightVariable);

        BinaryExpression innerImplies = new BinaryExpression(leftMembers, BinaryExpression.Op.IMPLIES, exists);

        QuantifiedExpression innerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, leftVariables, innerImplies);

        Expression    sigExpression = translator.signaturesMap.get(field.sig).getConstantExpr();

        BinaryExpression member = new BinaryExpression(sigVariable.getConstantExpr(), BinaryExpression.Op.MEMBER, sigExpression);

        BinaryExpression outerImplies = new BinaryExpression(member, BinaryExpression.Op.IMPLIES, innerForAll);

        QuantifiedExpression outerForAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, outerImplies, sigVariable);

        translator.smtProgram.addAssertion(new Assertion(outerForAll));

        //ToDo: handle nested multiplicities
    }    

    private void translateRelationSomeMultiplicity(Sig.Field field, FunctionDeclaration declaration, ExprUnary exprUnary)
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
        if(exprUnary.sub instanceof ExprUnary && ((ExprUnary) exprUnary.sub).sub instanceof Sig)
        {

            FunctionDeclaration set1            = translator.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = translator.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            Sort fstSigSort = translator.signatureTranslator.getAncestorSig(field.sig) == Sig.SIGINT?translator.intSort:translator.atomSort;
            Sort sndSigSort = translator.signatureTranslator.getAncestorSig((Sig) ((ExprUnary) exprUnary.sub).sub) == Sig.SIGINT?translator.intSort:translator.atomSort;
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), fstSigSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);

            // (mkTuple x)
            MultiArityExpression    xTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr());

            // (mkTuple y)
            MultiArityExpression    yTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getConstantExpr());

            // (mkTuple x y)
            MultiArityExpression    xyTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,y.getConstantExpr());

            // (member (mkTuple x) Book)
            BinaryExpression        xMember         = new BinaryExpression(xTuple,BinaryExpression.Op.MEMBER, set1.getConstantExpr());

            // (member (mkTuple y) Addr)
            BinaryExpression        yMember         = new BinaryExpression(yTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (member (mkTuple x y) addr)
            BinaryExpression        xyMember        = new BinaryExpression(xyTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            BinaryExpression        and             = new BinaryExpression(yMember, BinaryExpression.Op.AND, xyMember);
            QuantifiedExpression    exists          = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and , y);
            BinaryExpression        implies         = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, exists);
            QuantifiedExpression    forall          = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies , x);
            translator.smtProgram.addAssertion(new Assertion(forall));
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateRelationOneMultiplicity(Sig.Field field, FunctionDeclaration declaration, ExprUnary exprUnary)
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
        if(exprUnary.sub instanceof ExprUnary && ((ExprUnary) exprUnary.sub).sub instanceof Sig)
        {

            FunctionDeclaration set1            = translator.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = translator.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            Sort fstSigSort = translator.signatureTranslator.getAncestorSig(field.sig) == Sig.SIGINT?translator.intSort:translator.atomSort;
            Sort sndSigSort = translator.signatureTranslator.getAncestorSig((Sig) ((ExprUnary) exprUnary.sub).sub) == Sig.SIGINT?translator.intSort:translator.atomSort;            
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), fstSigSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);

            // (mkTuple x)
            MultiArityExpression    xTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr());

            // (mkTuple y)
            MultiArityExpression    yTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getConstantExpr());

            // (mkTuple z)
            MultiArityExpression    zTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getConstantExpr());

            // (mkTuple x y)
            MultiArityExpression    xyTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,y.getConstantExpr());

            // (mkTuple x z)
            MultiArityExpression    xzTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,z.getConstantExpr());

            // (member (mkTuple x) Book)
            BinaryExpression        xMember         = new BinaryExpression(xTuple,BinaryExpression.Op.MEMBER, set1.getConstantExpr());

            // (member (mkTuple y) Addr)
            BinaryExpression        yMember         = new BinaryExpression(yTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (member (mkTuple z) Addr)
            BinaryExpression        zMember         = new BinaryExpression(zTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (= z y)
            BinaryExpression        zEqualsY        = new BinaryExpression(z.getConstantExpr(), BinaryExpression.Op.EQ, y.getConstantExpr());

            // (not (= z y))
            UnaryExpression         notZEqualsY     = new UnaryExpression(UnaryExpression.Op.NOT, zEqualsY);

            //(and 	(member (mkTuple z) Addr) (not (= z y)))
            BinaryExpression        and1            = new BinaryExpression(zMember, BinaryExpression.Op.AND, notZEqualsY);

            // (member (mkTuple x y) addr)
            BinaryExpression        xyMember        = new BinaryExpression(xyTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            // (member (mkTuple x z) addr)
            BinaryExpression        xzMember        = new BinaryExpression(xzTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            // (not (member (mkTuple x z) addr))
            UnaryExpression         notXZMember     = new UnaryExpression(UnaryExpression.Op.NOT, xzMember);

            // (=>  (and (member (mkTuple z) Addr) (not (= z y)))
            //      (not (member (mkTuple x z) addr)))
            BinaryExpression        implies1        = new BinaryExpression(and1, BinaryExpression.Op.IMPLIES, notXZMember);
            //(forall ((z Atom))
            //	(=> (and 	(member (mkTuple y) Addr)
            //				(not (= z y)))
            //		(not (member (mkTuple x z) addr))
            //	)
            QuantifiedExpression    forall1         = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies1 , z);
            BinaryExpression        and2            = new BinaryExpression(xyMember, BinaryExpression.Op.AND, forall1);

            BinaryExpression        and3            = new BinaryExpression(yMember, BinaryExpression.Op.AND, and2);

            QuantifiedExpression    exists          = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and3 , y);
            BinaryExpression        implies2        = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, exists);
            QuantifiedExpression    forall2         = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies2 , x);
            translator.smtProgram.addAssertion(new Assertion(forall2));
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateRelationLoneMultiplicity(Sig.Field field, FunctionDeclaration declaration, ExprUnary exprUnary)
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
        if(exprUnary.sub instanceof ExprUnary && ((ExprUnary) exprUnary.sub).sub instanceof Sig)
        {

            FunctionDeclaration set1            = translator.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = translator.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            Sort fstSigSort = translator.signatureTranslator.getAncestorSig(field.sig) == Sig.SIGINT?translator.intSort:translator.atomSort;
            Sort sndSigSort = translator.signatureTranslator.getAncestorSig((Sig) ((ExprUnary) exprUnary.sub).sub) == Sig.SIGINT?translator.intSort:translator.atomSort;                        
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), fstSigSort);
            BoundVariableDeclaration u          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), sndSigSort);

            // (mkTuple x)
            MultiArityExpression    xTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr());

            // (mkTuple x)
            MultiArityExpression    uTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, u.getConstantExpr());

            // (mkTuple y)
            MultiArityExpression    yTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getConstantExpr());

            // (mkTuple z)
            MultiArityExpression    zTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getConstantExpr());

            // (mkTuple x u)
            MultiArityExpression    xuTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,u.getConstantExpr());

            // (mkTuple x y)
            MultiArityExpression    xyTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,y.getConstantExpr());

            // (mkTuple x z)
            MultiArityExpression    xzTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getConstantExpr() ,z.getConstantExpr());

            // (member (mkTuple x) Book)
            BinaryExpression        xMember         = new BinaryExpression(xTuple,BinaryExpression.Op.MEMBER, set1.getConstantExpr());

            // (member (mkTuple u) Addr)
            BinaryExpression        uMember         = new BinaryExpression(uTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (member (mkTuple x u) addr)
            BinaryExpression        xuMember        = new BinaryExpression(xuTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            // (not (member (mkTuple x u) addr))
            UnaryExpression        notXUMember      = new UnaryExpression(UnaryExpression.Op.NOT, xuMember);
            // (=> (member (mkTuple u) Addr) (not (member (mkTuple x u) addr)))
            BinaryExpression        implies0        = new BinaryExpression(uMember, BinaryExpression.Op.IMPLIES, notXUMember);

            // (forall ((u Atom)) (=> (member (mkTuple u) Addr) (not (member (mkTuple x u) addr))))
            QuantifiedExpression        forall0         = new QuantifiedExpression(QuantifiedExpression.Op.FORALL,  implies0, u);

            // (member (mkTuple y) Addr)
            BinaryExpression        yMember         = new BinaryExpression(yTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (member (mkTuple z) Addr)
            BinaryExpression        zMember         = new BinaryExpression(zTuple,BinaryExpression.Op.MEMBER, set2.getConstantExpr());

            // (= z y)
            BinaryExpression        zEqualsY        = new BinaryExpression(z.getConstantExpr(), BinaryExpression.Op.EQ, y.getConstantExpr());

            // (not (= z y))
            UnaryExpression         notZEqualsY     = new UnaryExpression(UnaryExpression.Op.NOT, zEqualsY);

            //(and 	(member (mkTuple z) Addr) (not (= z y)))
            BinaryExpression        and1            = new BinaryExpression(zMember, BinaryExpression.Op.AND, notZEqualsY);

            // (member (mkTuple x y) addr)
            BinaryExpression        xyMember        = new BinaryExpression(xyTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            // (member (mkTuple x z) addr)
            BinaryExpression        xzMember        = new BinaryExpression(xzTuple,BinaryExpression.Op.MEMBER, declaration.getConstantExpr());

            // (not (member (mkTuple x z) addr))
            UnaryExpression         notXZMember     = new UnaryExpression(UnaryExpression.Op.NOT, xzMember);

            // (=>  (and (member (mkTuple z) Addr) (not (= z y)))
            //      (not (member (mkTuple x z) addr)))
            BinaryExpression        implies1        = new BinaryExpression(and1, BinaryExpression.Op.IMPLIES, notXZMember);
            //(forall ((z Atom))
            //	(=> (and 	(member (mkTuple z) Addr)
            //				(not (= z y)))
            //		(not (member (mkTuple x z) addr))
            //	)
            QuantifiedExpression    forall1         = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies1 , z);
            BinaryExpression        and2            = new BinaryExpression(xyMember, BinaryExpression.Op.AND, forall1);

            BinaryExpression        and3            = new BinaryExpression(yMember, BinaryExpression.Op.AND, and2);

            QuantifiedExpression    exists          = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and3 , y);
            BinaryExpression        or              = new BinaryExpression(forall0, BinaryExpression.Op.OR, exists);
            BinaryExpression        implies2        = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, or);
            QuantifiedExpression    forall2         = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies2 , x);
            translator.smtProgram.addAssertion(new Assertion(forall2));
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }
}
