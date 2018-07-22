/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.Alloy2SMTLogger;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    final Alloy2SMTLogger LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    
    final String                    atom;
    final CompModule                alloyModel;
    final List<Sig>                 reachableSigs;
    final List<Sig>                 topLevelSigs;
    final SetSort                   setOfUnaryAtomSort;
    final SetSort                   setOfBinaryAtomSort;
    final UninterpretedSort         atomSort;
    final TupleSort                 unaryAtomSort;
    final TupleSort                 binaryAtomSort;
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;
    final UnaryExpression           universe;
    final UnaryExpression           none;
    final FunctionDeclaration       identity;

    Map<Sig,FunctionDeclaration>        signaturesMap   = new HashMap<>();
    Map<Sig.Field,FunctionDeclaration>  fieldsMap       = new HashMap<>();


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
        this.signatureTranslator    = new SignatureTranslator(this);
        this.exprTranslator         = new ExprTranslator(this);
        this.universe               = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryAtomSort);
        this.none                   = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryAtomSort);
        this.identity               = new FunctionDeclaration("identity", setOfBinaryAtomSort );
    }

    public SMTProgram execute()
    {
        translateSpecialFunctions();
        this.signatureTranslator.translate();
        translateFacts();

        translateSpecialAssertions();
        return this.smtProgram;
    }

    private void translateSpecialFunctions()
    {
        this.smtProgram.addFunctionDeclaration(this.identity);
    }

    private void translateSpecialAssertions()
    {
        BoundVariableDeclaration    a       = new BoundVariableDeclaration("_x1", atomSort);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr());
        BinaryExpression            memberA = new BinaryExpression(tupleA, BinaryExpression.Op.MEMBER, this.universe);

        BoundVariableDeclaration    b       = new BoundVariableDeclaration("_x2", atomSort);
        MultiArityExpression        tupleB  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,b.getConstantExpr());
        BinaryExpression            memberB = new BinaryExpression(tupleB, BinaryExpression.Op.MEMBER, this.universe);

        BinaryExpression            and     = new BinaryExpression(memberA, BinaryExpression.Op.AND, memberB);

        MultiArityExpression        tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr(), b.getConstantExpr());

        BinaryExpression            member  = new BinaryExpression(tupleAB, BinaryExpression.Op.MEMBER, this.identity.getConstantExpr());

        BinaryExpression            equals  = new BinaryExpression(a.getConstantExpr(), BinaryExpression.Op.EQ, b.getConstantExpr());

        BinaryExpression            equiv   = new BinaryExpression(member, BinaryExpression.Op.EQ, equals);

        BinaryExpression            implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES , equiv);


        QuantifiedExpression        forall  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b);

        this.smtProgram.addAssertion(new Assertion(forall));
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
        Map<String, ConstantExpression> variablesScope = new HashMap<>();
        Expression expression = this.exprTranslator.translateExpr(factExpr, variablesScope);
        this.smtProgram.addAssertion(new Assertion(factName, expression));
    }
}
