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
import java.util.Arrays;
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
    final SetSort                   setOfUnaryIntSort;
    final SetSort                   setOfTernaryIntSort;    
    final UninterpretedSort         atomSort;
    final IntSort                   intSort;
    final TupleSort                 unaryAtomSort;
    final TupleSort                 unaryIntSort;
    final TupleSort                 binaryAtomSort;      
    final TupleSort                 ternaryIntSort;
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;
    final FunctionDeclaration       atomUniv;
    final UnaryExpression           intUniv;
    final UnaryExpression           atomNone;
    final FunctionDeclaration       atomIden;
    final FunctionDeclaration       intUnivExpr;
    final UnaryExpression           intNone;
    final FunctionDeclaration       intIden;    

    
    Map<BinaryExpression.Op, FunctionDefinition>    comparisonOps;
    Map<BinaryExpression.Op, ConstantExpression>    arithOps;
    Map<Sig,FunctionDeclaration>        signaturesMap   = new HashMap<>();
    Map<Sig.Field,FunctionDeclaration>  fieldsMap       = new HashMap<>();


    public Alloy2SMTTranslator(CompModule alloyModel)
    {
        this.smtProgram             = new SMTProgram();        
        this.atom                   = "Atom";
        this.intSort                = new IntSort();
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.atomSort               = new UninterpretedSort(this.atom);
        this.unaryAtomSort          = new TupleSort(this.atomSort);
        this.binaryAtomSort         = new TupleSort(this.atomSort, this.atomSort);
        this.unaryIntSort           = new TupleSort(this.intSort);
        this.ternaryIntSort         = new TupleSort(this.intSort, this.intSort, this.intSort);
        this.setOfUnaryAtomSort     = new SetSort(this.unaryAtomSort);
        this.setOfUnaryIntSort      = new SetSort(this.unaryIntSort);
        this.setOfBinaryAtomSort    = new SetSort(this.binaryAtomSort);
        this.setOfTernaryIntSort    = new SetSort(this.ternaryIntSort);
        this.signatureTranslator    = new SignatureTranslator(this);
        this.exprTranslator         = new ExprTranslator(this);
        this.atomUniv               = new FunctionDeclaration("atomUniv", setOfUnaryAtomSort);
        this.atomNone               = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryAtomSort);
        this.atomIden               = new FunctionDeclaration("atomIden", setOfBinaryAtomSort );        
        this.intUniv                = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryIntSort);        
        this.intUnivExpr            = new FunctionDeclaration("intUniv", setOfUnaryIntSort);
        this.intIden                = new FunctionDeclaration("intIden", setOfUnaryIntSort );
        this.intNone                = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryIntSort);
        this.comparisonOps          = new HashMap<>();  
        this.arithOps               = new HashMap<>();
        this.signaturesMap.put(Sig.SIGINT, this.atomUniv);
    }

    public SMTProgram execute()
    {
        translateSpecialFunctions();
        this.signatureTranslator.translateSigs();
        translateFacts();
        translateSpecialAssertions();
        return this.smtProgram;
    }

    private void translateSpecialFunctions()
    {
        this.smtProgram.addFunctionDeclaration(this.atomUniv);
        this.smtProgram.addFunctionDeclaration(this.atomIden);
    }

    private void translateSpecialAssertions()
    {
        BoundVariableDeclaration    a       = new BoundVariableDeclaration("_x1", atomSort);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr());
        BinaryExpression            memberA = new BinaryExpression(tupleA, BinaryExpression.Op.MEMBER, this.atomUniv.getConstantExpr());

        BoundVariableDeclaration    b       = new BoundVariableDeclaration("_x2", atomSort);
        MultiArityExpression        tupleB  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,b.getConstantExpr());
        BinaryExpression            memberB = new BinaryExpression(tupleB, BinaryExpression.Op.MEMBER, this.atomUniv.getConstantExpr());

        BinaryExpression            and     = new BinaryExpression(memberA, BinaryExpression.Op.AND, memberB);

        MultiArityExpression        tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr(), b.getConstantExpr());

        BinaryExpression            member  = new BinaryExpression(tupleAB, BinaryExpression.Op.MEMBER, this.atomIden.getConstantExpr());

        BinaryExpression            equals  = new BinaryExpression(a.getConstantExpr(), BinaryExpression.Op.EQ, b.getConstantExpr());

        BinaryExpression            equiv   = new BinaryExpression(member, BinaryExpression.Op.EQ, equals);

        BinaryExpression            implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES , equiv);
        
        QuantifiedExpression        forall  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b);

        this.smtProgram.addAssertion(new Assertion(new BinaryExpression(this.atomUniv.getConstantExpr(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryAtomSort))));
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
