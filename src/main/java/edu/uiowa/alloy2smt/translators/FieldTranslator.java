package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class FieldTranslator
{

    private final Alloy2SMTTranslator translator;

    public FieldTranslator(Alloy2SMTTranslator translator)
    {
        this.translator = translator;
    }


    void translate(Sig.Field field)
    {

        String              fieldName   = TranslatorUtils.sanitizeName(field.sig.label + "/" + field.label);
        TupleSort tupleSort   = new TupleSort(Collections.nCopies(field.type().arity(), translator.atomSort));
        SetSort setSort     = new SetSort(tupleSort);
        FunctionDeclaration declaration = new FunctionDeclaration(fieldName, setSort);

        // declare a variable for the field
        translator.smtProgram.addFunctionDeclaration(declaration);
        translator.fieldsMap.put(field, declaration);

        // a field relation is a subset of the product of its signatures
        List<Sig> fieldSignatures     =  field.type().fold().stream().flatMap(List::stream).collect(Collectors.toList());

        /* alloy: sig Book{addr: Name -> lone Addr}
         *  smt  : (assert (subset addr (product (product Book Name) Addr)))
         */
        ConstantExpression first   = translator.signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();
        ConstantExpression second  = translator.signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();
        BinaryExpression product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldSignatures.size(); i++)
        {
            ConstantExpression expr = translator.signaturesMap.get(fieldSignatures.get(i)).getConstantExpr();
            product                 = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);
        }

        ConstantExpression fieldExpr   = declaration.getConstantExpr();
        BinaryExpression    subset      = new BinaryExpression(fieldExpr, BinaryExpression.Op.SUBSET, product);
        Assertion           assertion   = new Assertion(subset);

        translator.smtProgram.addAssertion(assertion);

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
            translateBinaryMultiplicities((ExprBinary) expr, field, declaration, 0);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateBinaryMultiplicities(ExprBinary exprBinary, Sig.Field field, FunctionDeclaration declaration, int index)
    {
        switch (exprBinary.op)
        {
            case ARROW              : break; // no assertion needed
            case ANY_ARROW_SOME     :
            case ANY_ARROW_ONE      :
            case ANY_ARROW_LONE     :
            case SOME_ARROW_ANY     :
            case SOME_ARROW_SOME    :
            case SOME_ARROW_ONE     :
            case SOME_ARROW_LONE    :
            case ONE_ARROW_ANY      :
            case ONE_ARROW_SOME     :
            case ONE_ARROW_ONE      : translateOneArrowOne(field, declaration, index);
            case ONE_ARROW_LONE     :
            case LONE_ARROW_ANY     :
            case LONE_ARROW_SOME    :
            case LONE_ARROW_ONE     :
            case LONE_ARROW_LONE    :
            case ISSEQ_ARROW_LONE   : break;
            default:
            {
                throw new UnsupportedOperationException();
            }
        }

        if(exprBinary.right instanceof ExprBinary)
        {
            translateBinaryMultiplicities((ExprBinary) exprBinary.right, field, declaration, index + 1);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private void translateOneArrowOne(Sig.Field field, FunctionDeclaration declaration, int index)
    {
        //(assert
        //	(forall ((x1 Atom) (x2 Atom) ... (xn Atom))
        //		(=> and (
        //                  (member (mkTuple x1) Set1)
        //                  (member (mkTuple x2) Set2)
        //                          ⋮
        //                  (member (mkTuple xi-1) Seti-1)
        //                          ⋮
        //                  (member (mkTuple xi+1) Seti+1)
        //                  (member (mkTuple xn) Setn)
        //          (and
        //			    (exists ((xi Atom))
        //				    (and
        //					    (member (mkTuple xi) Seti)
        //					    (member (mkTuple x1 ... xn) addr)
        //					    (forall ((z Atom))
        //						    (=> (and 	(member (mkTuple z) Seti)
        //									    (not (= z xi)))
        //							    (not (member (mkTuple x1 x2 ... xi-1 z xi+1 xn) addr))
        //						    )
        //					    )
        //				    )
        //			    )
        //			    (exists ((xi+1 Atom))
        //				    (and
        //					    (member (mkTuple xi+1) Seti+1)
        //					    (member (mkTuple x1 ... xn) addr)
        //					    (forall ((z Atom))
        //						    (=> (and 	(member (mkTuple z) Seti+1)
        //									    (not (= z xi+1)))
        //							    (not (member (mkTuple x1 x2 ... xi z xi+2 xn) addr))
        //						    )
        //					    )
        //				    )
        //			    )
        //          )
        //		)
        //	)
        //)
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
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);

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
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);

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
            BoundVariableDeclaration x          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration u          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(TranslatorUtils.getNewName(), translator.atomSort);

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
