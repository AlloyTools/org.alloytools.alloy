/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

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

    private Map<Sig,VariableDeclaration>    signaturesMap = new HashMap<>();

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
        translateSigsAndHierarchy();
        return this.smtProgram;
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
    
    private void translateSigsAndHierarchy() 
    {
        this.reachableSigs.forEach((sig) -> {

            VariableDeclaration variableDeclaration =  mkAndAddUnaryAtomRelation(Utils.sanitizeName(sig.toString()));
            this.signaturesMap.put(sig, variableDeclaration);
            // translate signature fields
            for(Sig.Field field : sig.getFields())
            {
                translateField(field);
            }
        });
    }

    private void translateField(Sig.Field field)
    {

        String              fieldName   = Utils.sanitizeName(field.sig.label + "/" + field.label);
        TupleSort           tupleSort   = new TupleSort(Collections.nCopies(field.type().arity(), this.atomSort));
        SetSort             setSort     = new SetSort(tupleSort);
        VariableDeclaration declaration = new VariableDeclaration(fieldName, setSort);

        // declare a variable for the field
        this.smtProgram.addVarDecl(declaration);

        // a field relation is a subset of the product of its signatures
        List<Sig>           fieldSignatures     =  field.type().fold().stream().flatMap(List::stream).collect(Collectors.toList());

        /* alloy: sig Book{addr: Name -> lone Addr}
        *  smt  : (assert (subset addr (product (product Book Name) Addr)))
        */
        VariableExpression  first   = new VariableExpression(signaturesMap.get(fieldSignatures.get(0)).getVarName());
        VariableExpression  second  = new VariableExpression(signaturesMap.get(fieldSignatures.get(1)).getVarName());
        BinaryExpression    product = new BinaryExpression(first, BinaryExpression.Op.PRODUCT, second);

        for(int i = 2; i < fieldSignatures.size(); i++)
        {
            VariableExpression  expr = new VariableExpression(signaturesMap.get(fieldSignatures.get(i)).getVarName());
            product                  = new BinaryExpression(product, BinaryExpression.Op.PRODUCT, expr);
        }

        VariableExpression  fieldExpr   = new VariableExpression(declaration.getVarName());
        BinaryExpression    subset      = new BinaryExpression(fieldExpr, BinaryExpression.Op.SUBSET, product);
        Assertion           assertion   = new Assertion(subset);

        this.smtProgram.addAssertion(assertion);

        // translate multiplicities
        translateMultiplicities(field, declaration);
    }

    private void translateMultiplicities(Sig.Field field, VariableDeclaration declaration)
    {
        Expr expr = field.decl().expr;
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary) expr;
            switch (exprUnary.op)
            {
                case SOMEOF:
                case LONEOF:
                case ONEOF:
                {
                    //(assert
                    //	(forall ((x Atom))
                    //		(=> (member (mkTuple x) Book)
                    //			(exists ((y Atom))
                    //				(and
                    //					(member (mkTuple y) Addr)
                    //					(member (mkTuple x y) addr)
                    //					(forall ((z Atom))
                    //						(=> (and 	(member (mkTuple y) Addr)
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

                        VariableDeclaration     set1            = this.signaturesMap.get(field.sig);
                        VariableDeclaration     set2            = this.signaturesMap.get((Sig) ((ExprUnary) exprUnary.sub).sub);
                        VariableDeclaration     x               = new VariableDeclaration(Utils.getNewVariableName(), this.atomSort);
                        VariableDeclaration     y               = new VariableDeclaration(Utils.getNewVariableName(), this.atomSort);
                        VariableDeclaration     z               = new VariableDeclaration(Utils.getNewVariableName(), this.atomSort);

                        // (mkTuple x)
                        MultiArityExpression    xTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVarExpr());
                        // (mkTuple y)
                        MultiArityExpression    yTuple          = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVarExpr());

                        // (mkTuple x y)
                        MultiArityExpression    xyTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVarExpr() ,y.getVarExpr());

                        // (mkTuple x z)
                        MultiArityExpression    xzTuple         = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVarExpr() ,z.getVarExpr());

                        // (member (mkTuple x) Book)
                        BinaryExpression        xMember         = new BinaryExpression(xTuple,BinaryExpression.Op.MEMBER, set1.getVarExpr());

                        // (member (mkTuple y) Addr)
                        BinaryExpression        yMember         = new BinaryExpression(yTuple,BinaryExpression.Op.MEMBER, set2.getVarExpr());
                        // (= z y)
                        BinaryExpression        zEqualsY        = new BinaryExpression(z.getVarExpr(), BinaryExpression.Op.EQ, y.getVarExpr());
                        // (not (= z y))
                        UnaryExpression         notZEqualsY     = new UnaryExpression(UnaryExpression.Op.NOT, zEqualsY);

                        //(and 	(member (mkTuple y) Addr) (not (= z y)))
                        BinaryExpression        and1            = new BinaryExpression(yMember, BinaryExpression.Op.AND, notZEqualsY);

                        // (member (mkTuple x y) addr)
                        BinaryExpression        xyMember        = new BinaryExpression(xyTuple,BinaryExpression.Op.MEMBER, declaration.getVarExpr());

                        // (member (mkTuple x z) addr)
                        BinaryExpression        xzMember        = new BinaryExpression(xzTuple,BinaryExpression.Op.MEMBER, declaration.getVarExpr());

                        // (not (member (mkTuple x z) addr))

                        UnaryExpression         notXZMember     = new UnaryExpression(UnaryExpression.Op.NOT, xzMember);
                        // (=>  (and (member (mkTuple y) Addr) (not (= z y)))
                        //      (not (member (mkTuple x z) addr)))
                        BinaryExpression    implies1        = new BinaryExpression(and1, BinaryExpression.Op.IMPLIES, notXZMember);
                        //(forall ((z Atom))
                        //	(=> (and 	(member (mkTuple y) Addr)
                        //				(not (= z y)))
                        //		(not (member (mkTuple x z) addr))
                        //	)
                        QuantifiedExpression forall1        = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies1 , z);
                        BinaryExpression    and2            = new BinaryExpression(xyMember, BinaryExpression.Op.AND, forall1);

                        BinaryExpression    and3            = new BinaryExpression(yMember, BinaryExpression.Op.AND, and2);

                        QuantifiedExpression exists         = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and3 , y);
                        BinaryExpression    implies2        = new BinaryExpression(xMember, BinaryExpression.Op.IMPLIES, exists);
                        QuantifiedExpression forall2        = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies2 , x);
                        this.smtProgram.addAssertion(new Assertion(forall2));
                    }
                    else
                    {
                        throw new UnsupportedOperationException();
                    }
                } break;
                case SETOF:
                case EXACTLYOF:
                default:
                {
                    throw new UnsupportedOperationException("Not supported yet");
                }
            }
        }
        else if (expr instanceof ExprBinary)
        {
            ExprBinary exprBinary = (ExprBinary) expr;
            switch (exprBinary.op)
            {
                case ARROW:
                case ANY_ARROW_SOME:
                case ANY_ARROW_ONE:
                {

                }
                break;
                case ANY_ARROW_LONE:
                case SOME_ARROW_ANY:
                case SOME_ARROW_SOME:
                case SOME_ARROW_ONE:
                case SOME_ARROW_LONE:
                case ONE_ARROW_ANY:
                case ONE_ARROW_SOME:
                case ONE_ARROW_ONE:
                case ONE_ARROW_LONE:
                case LONE_ARROW_ANY:
                case LONE_ARROW_SOME:
                case LONE_ARROW_ONE:
                case LONE_ARROW_LONE:
                case ISSEQ_ARROW_LONE:
                default:
                {
                    throw new UnsupportedOperationException();
                }
            }
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    private VariableDeclaration mkAndAddUnaryAtomRelation(String varName)
    {
        VariableDeclaration variable = null;
        if(varName != null)
        {
            variable = new VariableDeclaration(varName, this.setOfUnaryAtomSort);
            this.smtProgram.addVarDecl(variable);
        }
        return variable;
    }
    
    private void mkAndAddBinaryAtomRelation(String varName) 
    {
        if(varName != null) 
        {
            this.smtProgram.addVarDecl(new VariableDeclaration(varName, this.setOfBinaryAtomSort));
        }        
    }    
    
    private void addToVarDecl(VariableDeclaration varDecl) 
    {
        if(varDecl != null) 
        {
            this.smtProgram.addVarDecl(varDecl);
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
