/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    private final Alloy2SMTLogger   LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    
    private final String                    atom;
    private final CompModule                alloyModel;
    private final List<Sig>                 reachableSigs;
    private final List<Sig>                 topLevelSigs;
    private final SetSort                   setOfUnaryAtomSort;
    private final SetSort                   setOfBinaryAtomSort;
    private final UninterpretedSort         atomSort;
    private final TupleSort                 unaryAtomSort;
    private final TupleSort                 binaryAtomSort;

    private Map<Sig,FunctionDeclaration>    signaturesMap = new HashMap<>();

    public Alloy2SMTTranslator(CompModule alloyModel)
    {
        this.smtProgram             = new SMTProgram();
        
        this.atom                   = "Atom";
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.atomSort               = new UninterpretedSort(this.atom);
        this.unaryAtomSort          = new TupleSort(this.atomSort);
        this.binaryAtomSort         = new TupleSort(this.atomSort, this.atomSort);
        this.setOfUnaryAtomSort     = new SetSort(this.unaryAtomSort);
        this.setOfBinaryAtomSort    = new SetSort(this.binaryAtomSort);
    }

    public SMTProgram execute()
    {        
        collectReachableSigs();
        translateSignatures();
        translateSignatureHierarchies();
        translateFacts();
        return this.smtProgram;
    }

    private void translateFacts()
    {
        for (Pair<String, Expr> pair :this.alloyModel.getAllFacts() )
        {
            translateFact(pair.a, pair.b);
        }
    }

    private void translateFact(String factName, Expr factExpr)
    {
        Expression expression = translateExpr(factExpr);
        this.smtProgram.addAssertion(new Assertion(factName, expression));
    }

    private Expression translateExpr(Expr expr)
    {
        if(expr instanceof ExprUnary)
        {
            return translateExprUnary((ExprUnary) expr);
        }
        throw new UnsupportedOperationException();
    }

    private Expression translateExprUnary(ExprUnary exprUnary)
    {
        switch (exprUnary.op)
        {
            case NOOP   : return translateNoop(exprUnary);
            case NO     : return translateNo(exprUnary);
            default:
            {
                throw new UnsupportedOperationException("Not supported yet");
            }
        }
    }



    private Expression translateNoop(ExprUnary exprUnary)
    {
        if(exprUnary.sub instanceof Sig)
        {
            return this.signaturesMap.get(exprUnary.sub).getConstantExpr();
        }

        if(exprUnary.sub instanceof ExprUnary)
        {
            return translateExprUnary((ExprUnary) exprUnary.sub);
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateNo(ExprUnary exprUnary)
    {
        BoundVariableDeclaration    variable    = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
        MultiArityExpression        tuple       = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable.getConstantExpr());
        Expression                  set         = translateExpr(exprUnary.sub);
        Expression                  expression  = null;

        if(set instanceof ConstantExpression)
        {
            BinaryExpression member         = new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, set);
            expression                      = new UnaryExpression(UnaryExpression.Op.NOT, member);
        }
        else
        {
            throw new UnsupportedOperationException();
        }

        QuantifiedExpression        forall      = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, expression, variable);
        return forall;
    }
    private void translateSignatureHierarchies()
    {
        for (Sig sig: this.topLevelSigs)
        {
            Sig.PrimSig primSig = (Sig.PrimSig) sig;
            translateDisjointSignatures(primSig);
            if(primSig.isAbstract != null)
            {
                SafeList<Sig.PrimSig> children = primSig.children();
                if(children.size() == 1)
                {
                    Expression          left        = this.signaturesMap.get(sig).getConstantExpr();
                    Expression          right       = this.signaturesMap.get(children.get(0)).getConstantExpr();
                    BinaryExpression    equality    = new BinaryExpression(left, BinaryExpression.Op.EQ, right);
                    this.smtProgram.addAssertion(new Assertion(equality));
                }
                else if(children.size() > 1)
                {

                    Expression          left        = this.signaturesMap.get(children.get(0)).getConstantExpr();
                    Expression          right       = this.signaturesMap.get(children.get(1)).getConstantExpr();
                    BinaryExpression    union       = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                    for(int i = 2; i < children.size(); i++)
                    {
                        Expression      expression  = this.signaturesMap.get(children.get(i)).getConstantExpr();
                        union                       = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                    }

                    Expression          leftExpr    = this.signaturesMap.get(sig).getConstantExpr();
                    BinaryExpression    equality    = new BinaryExpression(leftExpr, BinaryExpression.Op.EQ, union);
                    this.smtProgram.addAssertion(new Assertion(equality));
                }
            }
        }
    }

    private void translateDisjointSignatures(Sig.PrimSig primSig)
    {
        for (int i = 0; i < primSig.children().size(); i++)
        {
            Expression      left    = this.signaturesMap.get(primSig.children().get(i)).getConstantExpr();

            UnaryExpression emptySet   = new UnaryExpression(UnaryExpression.Op.EMPTYSET, this.signaturesMap.get(primSig.children().get(i)).getOutputSort());

            for (int j = i + 1 ; j < primSig.children().size(); j++)
            {
                Expression          right       = this.signaturesMap.get(primSig.children().get(j)).getConstantExpr();
                BinaryExpression    disjoint    = new BinaryExpression(left, BinaryExpression.Op.INTERSECTION, right);
                
                BinaryExpression    equality    = new BinaryExpression(disjoint, BinaryExpression.Op.EQ, emptySet);
                this.smtProgram.addAssertion(new Assertion(equality));
            }
        }
    }

    private void collectReachableSigs() 
    {
        LOGGER.printInfo("********************** COLLECT REACHABLE SIGNATURES **********************");
        
        for(Sig sig : this.alloyModel.getAllSigs()) 
        {
            if(sig.isTopLevel()) 
            {
                this.topLevelSigs.add(sig);
            }
            this.reachableSigs.add(sig);
        }
    } 
    
    private void translateSignatures()
    {
        this.reachableSigs.forEach((sig) ->
        {
            FunctionDeclaration functionDeclaration =  declareUnaryAtomFunction(Utils.sanitizeName(sig.toString()));
            this.signaturesMap.put(sig, functionDeclaration);

            // if sig extends another signature
            if(! sig.isTopLevel())
            {
                translateSigSubsetParent(sig, functionDeclaration);
            }

            if (sig.isOne != null)
            {
                translateSignatureOneMultiplicity(sig);
            }

            if (sig.isLone != null)
            {
                translateSignatureLoneMultiplicity(sig);
            }

            if (sig.isSome != null)
            {
                translateSignatureSomeMultiplicity(sig);
            }

            // translate signature fields
            for(Sig.Field field : sig.getFields())
            {
                translateField(field);
            }
        });
    }

    private void translateSignatureOneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = this.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.EQ, declaration.getConstantExpr());
        this.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureLoneMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = this.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(signature.getConstantExpr(), BinaryExpression.Op.SUBSET, declaration.getConstantExpr());
        this.smtProgram.addAssertion(new Assertion(subset));
    }

    private void translateSignatureSomeMultiplicity(Sig sig)
    {
        FunctionDeclaration signature = this.signaturesMap.get(sig);

        FunctionDeclaration declaration = generateAuxiliarySetNAtoms(signature);

        BinaryExpression subset   = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.SUBSET, signature.getConstantExpr());
        this.smtProgram.addAssertion(new Assertion(subset));
    }

    private FunctionDeclaration generateAuxiliarySetNAtoms(FunctionDeclaration signature)
    {
        List<Expression> expressions = declareNDistinctConstants(this.atomSort, 1);

        FunctionDeclaration declaration = new FunctionDeclaration(Utils.getNewSet(), signature.getOutputSort());

        this.smtProgram.addFunctionDeclaration(declaration);

        Expression set = new UnaryExpression(UnaryExpression.Op.SINGLETON, expressions.get(expressions.size() - 1));

        if(expressions.size() > 1)
        {
            List<Expression> atoms = Arrays.asList(set);

            for(int i = expressions.size() - 2; i >= 0; i--)
            {
                atoms.add(expressions.get(i));
            }

            set = new MultiArityExpression(MultiArityExpression.Op.INSERT, atoms);
        }

        BinaryExpression equality = new BinaryExpression(declaration.getConstantExpr(), BinaryExpression.Op.EQ, set);

        this.smtProgram.addAssertion(new Assertion(equality));
        return declaration;
    }

    private List<Expression> declareNDistinctConstants(Sort sort,int n)
    {
        List<Expression> expressions = new ArrayList<>();
        if(n > 0)
        {
            for (int i = 0; i < n; i++)
            {
                ConstantDeclaration constantDeclaration = new ConstantDeclaration(Utils.getNewAtom(), sort);
                MultiArityExpression makeTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, constantDeclaration.getConstantExpr());
                expressions.add(makeTuple);
                this.smtProgram.addConstantDeclaration(constantDeclaration);
            }

            if (n > 1)
            {
                MultiArityExpression distinct = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, expressions);
                this.smtProgram.addAssertion(new Assertion(distinct));
            }
        }
        else
        {
            LOGGER.printSevere("Argument n should be greater than 0");
        }
        return expressions;
    }

    private void translateSigSubsetParent(Sig sig, FunctionDeclaration functionDeclaration)
    {
        if(sig instanceof Sig.PrimSig)
        {
            Sig                 parent              = ((Sig.PrimSig) sig).parent;
            FunctionDeclaration parentDeclaration   = this.signaturesMap.get(parent);
            BinaryExpression    subsetExpression    = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
            this.smtProgram.addAssertion(new Assertion(subsetExpression));
        }
        else
        {
            List<Sig> parents             = ((Sig.SubsetSig) sig).parents;
            if(parents.size() == 1)
            {
                FunctionDeclaration parentDeclaration   = this.signaturesMap.get(parents.get(0));
                BinaryExpression    subset              = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, parentDeclaration.getConstantExpr());
                this.smtProgram.addAssertion(new Assertion(subset));
            }
            else
            {
                Expression          left    = this.signaturesMap.get(parents.get(0)).getConstantExpr();
                Expression          right   = this.signaturesMap.get(parents.get(1)).getConstantExpr();
                BinaryExpression    union   = new BinaryExpression(left, BinaryExpression.Op.UNION, right);

                for (int i = 2; i < parents.size(); i++)
                {
                    Expression expression   = this.signaturesMap.get(parents.get(i)).getConstantExpr();
                    union                   = new BinaryExpression(union, BinaryExpression.Op.UNION, expression);
                }

                BinaryExpression subset     = new BinaryExpression(functionDeclaration.getConstantExpr(), BinaryExpression.Op.SUBSET, union);
                this.smtProgram.addAssertion(new Assertion(subset));
            }
        }
    }

    private void translateField(Sig.Field field)
    {

        String              fieldName   = Utils.sanitizeName(field.sig.label + "/" + field.label);
        TupleSort           tupleSort   = new TupleSort(Collections.nCopies(field.type().arity(), this.atomSort));
        SetSort             setSort     = new SetSort(tupleSort);
        FunctionDeclaration declaration = new FunctionDeclaration(fieldName, setSort);

        // declare a variable for the field
        this.smtProgram.addFunctionDeclaration(declaration);

        // a field relation is a subset of the product of its signatures
        List<Sig>           fieldSignatures     =  field.type().fold().stream().flatMap(List::stream).collect(Collectors.toList());

        /* alloy: sig Book{addr: Name -> lone Addr}
        *  smt  : (assert (subset addr (product (product Book Name) Addr)))
        */
        ConstantExpression first   = signaturesMap.get(fieldSignatures.get(0)).getConstantExpr();
        ConstantExpression second  = signaturesMap.get(fieldSignatures.get(1)).getConstantExpr();
        BinaryExpression    product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldSignatures.size(); i++)
        {
            ConstantExpression expr = signaturesMap.get(fieldSignatures.get(i)).getConstantExpr();
            product                  = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);
        }

        ConstantExpression fieldExpr   = declaration.getConstantExpr();
        BinaryExpression    subset      = new BinaryExpression(fieldExpr, BinaryExpression.Op.SUBSET, product);
        Assertion           assertion   = new Assertion(subset);

        this.smtProgram.addAssertion(assertion);

        // translate multiplicities
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
                case EXACTLYOF  : break; //ToDo: review this case
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

            FunctionDeclaration set1            = this.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = this.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            BoundVariableDeclaration x          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);

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
            this.smtProgram.addAssertion(new Assertion(forall));
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

            FunctionDeclaration set1            = this.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = this.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            BoundVariableDeclaration x          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);

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
            this.smtProgram.addAssertion(new Assertion(forall2));
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

            FunctionDeclaration set1            = this.signaturesMap.get(field.sig);
            FunctionDeclaration set2            = this.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
            BoundVariableDeclaration x          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration u          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration y          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);
            BoundVariableDeclaration z          = new BoundVariableDeclaration(Utils.getNewName(), this.atomSort);

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
            this.smtProgram.addAssertion(new Assertion(forall2));
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private FunctionDeclaration declareUnaryAtomFunction(String varName)
    {
        FunctionDeclaration declaration = null;
        if(varName != null)
        {
            declaration = new FunctionDeclaration(varName, this.setOfUnaryAtomSort);
            this.smtProgram.addFunctionDeclaration(declaration);
        }
        return declaration;
    }
    
    private void mkAndAddBinaryAtomRelation(String varName) 
    {
        if(varName != null) 
        {
            this.smtProgram.addFunctionDeclaration(new FunctionDeclaration(varName, this.setOfBinaryAtomSort));
        }        
    }    
    
    private void addToVarDecl(FunctionDeclaration varDecl)
    {
        if(varDecl != null) 
        {
            this.smtProgram.addFunctionDeclaration(varDecl);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null variable declaration!");
        }
    }
    
    private void addToFcnDecl(FunctionDeclaration fcnDecl) 
    {
        if(fcnDecl != null) 
        {
            this.smtProgram.addFcnDecl(fcnDecl);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null function declaration!");
        }
    }    
    
    private void addToFcnDef(FunctionDefinition fcnDef) 
    {
        if(fcnDef != null) 
        {
            this.smtProgram.addFcnDef(fcnDef);
        }
        else 
        {
            LOGGER.printSevere("Try to add a null function declaration!");
        }
    }    
}
