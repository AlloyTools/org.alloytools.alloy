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
    final SetSort                   setOfUnaryIntSort;
    final SetSort                   setOfTernaryIntSort;    
    final IntSort                   intSort;
    final TupleSort                 unaryAtomSort;
    final TupleSort                 unaryIntSort;
    final TupleSort                 binaryAtomSort;      
    final TupleSort                 ternaryIntSort;
    final UninterpretedSort         atomSort;    
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;
    final FunctionDeclaration       atomUniv;
    final UnaryExpression           intUniv;
    final FunctionDeclaration       atomNone;
    final FunctionDeclaration       atomIden;
    final FunctionDeclaration       intUnivExpr;
    final UnaryExpression           intNone;
    final FunctionDeclaration       intIden;    
    
    Map<Sig, Sort>                                  sigSortMap;
    Map<String, String>                             funcNamesMap;
    Map<String, FunctionDefinition>                 funcDefsMap;    
    Map<Sig, FunctionDeclaration>                   signaturesMap;
    Map<Sig.Field, FunctionDeclaration>             fieldsMap;    
    Map<BinaryExpression.Op, FunctionDefinition>    comparisonOps;
    Map<BinaryExpression.Op, ConstantExpression>    arithOps;
    Map<Sig, Expr>                                  sigFacts;
    List<BoundVariableDeclaration>                  existentialBdVars;
    Expression                                      auxExpr = null;


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
        this.atomNone               = new FunctionDeclaration("atomNone", setOfUnaryAtomSort);        
        this.atomIden               = new FunctionDeclaration("atomIden", setOfBinaryAtomSort );        
        this.intUniv                = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryIntSort);        
        this.intUnivExpr            = new FunctionDeclaration("intUniv", setOfUnaryIntSort);
        this.intIden                = new FunctionDeclaration("intIden", setOfUnaryIntSort );
        this.intNone                = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryIntSort);
        this.comparisonOps          = new HashMap<>();  
        this.arithOps               = new HashMap<>();
        this.signaturesMap          = new HashMap<>();
        this.funcNamesMap           = new HashMap<>();
        this.funcDefsMap            = new HashMap<>();
        this.fieldsMap              = new HashMap<>();
        this.sigFacts               = new HashMap<>();
        this.existentialBdVars      = new ArrayList<>();
        this.sigSortMap             = new HashMap<>();

        this.signaturesMap.put(Sig.UNIV, this.atomUniv);        
    }

    public SMTProgram execute(String assertion)
    {
        translateSpecialFunctions();
        this.signatureTranslator.translateSigs();
        translateFuncsAndPreds();
        translateFacts();
        translateAssertions(assertion);
        translateSpecialAssertions();
        return this.smtProgram;
    }

    private void translateSpecialFunctions()
    {
        this.smtProgram.addFunctionDeclaration(this.atomNone);
        this.smtProgram.addFunctionDeclaration(this.atomUniv);
        this.smtProgram.addFunctionDeclaration(this.atomIden);
    }

    private void translateSpecialAssertions()
    {
        // Axiom for identity relation
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
        
        QuantifiedExpression        idenSemantics  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b);

        this.smtProgram.addAssertion(new Assertion(new BinaryExpression(this.atomNone.getConstantExpr(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion(new BinaryExpression(this.atomUniv.getConstantExpr(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion(idenSemantics));
    }

    private void translateFacts()
    {
        for (Pair<String, Expr> pair :this.alloyModel.getAllFacts() )
        {
            translateFact(pair.a, pair.b);
        }
    }
    
    private void translateAssertions(String assertion)
    {
        if(assertion == null)
        {
            System.out.println("Translate the input Alloy model for checking its consistency!");
            return;
        }
        
        boolean hasAssertion = false;
        
        for (Pair<String, Expr> pair :this.alloyModel.getAllAssertions())
        {
            if(assertion.equals(pair.a))
            {
                System.out.println("Translate the input Alloy model for checking the assertion: " + pair.a);                
                translateAssertion(pair.a, pair.b);
                hasAssertion = true;
                break;
            }            
        }
        if(!hasAssertion)
        {
            System.out.println("The input Alloy model does not have an assertion with name: " + assertion);
        }
    }    
    
    private void translateFuncsAndPreds()
    {
        for (Func f :this.alloyModel.getAllFunc() )
        {
            if(f.label.equalsIgnoreCase("this/$$Default"))
            {
                continue;
            }
            translateFunc(f);
        }
    }    
    
    private void translateFunc(Func f)
    {        
        Sort    returnSort  = new BoolSort();        
        String  funcName    = TranslatorUtils.sanitizeName(f.label);                
        List<BoundVariableDeclaration>      bdVars  = new ArrayList<>();
        Map<String, Expression>     variablesScope  = new HashMap<>();
                
        // Save function name
        this.funcNamesMap.put(f.label, funcName);        
        // Declare input variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  bdVarName = n.label;
                Sort    bdVarSort = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.decls.get(i).expr));
                bdVars.add(new BoundVariableDeclaration(bdVarName, bdVarSort));
                variablesScope.put(bdVarName, new ConstantExpression(new ConstantDeclaration(bdVarName, bdVarSort)));
            }

        }
        // If the function is not predicate, we change its returned type.
        if(!f.isPred)
        {
            returnSort = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.returnDecl));
        }
        
        FunctionDefinition funcDef = new FunctionDefinition(funcName, bdVars, returnSort, 
                                                            this.exprTranslator.translateExpr(f.getBody(), variablesScope));
        this.funcDefsMap.put(funcName, funcDef);
        this.smtProgram.addFcnDef(funcDef);
    }    
    
    private int getArityofExpr(Expr expr)
    {
        return expr.type().arity();    
    }

    private void translateFact(String factName, Expr factExpr)
    {
        this.smtProgram.addAssertion(new Assertion(factName, this.exprTranslator.translateExpr(factExpr, new HashMap<>())));
    }
    
    private void translateAssertion(String assertionName, Expr assertionExpr)
    {
        Expression expression = this.exprTranslator.translateExpr(assertionExpr, new HashMap<>());
        this.smtProgram.addAssertion(new Assertion(assertionName, new UnaryExpression(UnaryExpression.Op.NOT, expression)));
    }    
}
