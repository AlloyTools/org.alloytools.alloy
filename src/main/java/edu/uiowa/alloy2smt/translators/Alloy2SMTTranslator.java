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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Alloy2SMTTranslator
{
    public final SMTProgram smtProgram;
    
    final Alloy2SMTLogger LOGGER = new Alloy2SMTLogger("Alloy2SMTTranslator");
    final String                    atom;
    final String                    intAtom;
    final CompModule                alloyModel;
    final List<Sig>                 reachableSigs;
    final List<Sig>                 topLevelSigs;
    final SetSort                   setOfUnaryAtomSort;
    final SetSort                   setOfBinaryAtomSort;
    final SetSort                   setOfUnaryIntSort;
    final SetSort                   setOfTernaryIntSort;    
    final IntSort                   intSort;
    final TupleSort                 unaryAtomSort;
    final TupleSort                 unaryIntAtomSort;    
    final TupleSort                 unaryIntSort;
    final TupleSort                 binaryAtomSort;      
    final TupleSort                 binaryIntAtomSort;          
    final TupleSort                 ternaryIntSort;
    final UninterpretedSort         atomSort;    
    final UninterpretedSort         intAtomSort;    
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;
    final FunctionDeclaration       atomUniv;
    final UnaryExpression           intUnivExpr;
    final FunctionDeclaration       atomNone;
    final FunctionDeclaration       atomIden;
    final FunctionDeclaration       intUniv;
    final UnaryExpression           intNone;
    final FunctionDeclaration       intIden;
    final FunctionDeclaration       valueOfIntAtom;    
    
    Map<String, String>                             funcNamesMap;
    Map<String, FunctionDefinition>                 funcDefsMap;    
    Map<Sig, FunctionDeclaration>                   signaturesMap;
    Map<Sig.Field, FunctionDeclaration>             fieldsMap;    
    Map<BinaryExpression.Op, FunctionDefinition>    comparisonOps;
    Map<BinaryExpression.Op, ConstantExpression>    arithOps;
    Map<Sig, Expr>                                  sigFacts;
    List<BoundVariableDeclaration>                  existentialBdVars;
    Expression                                      auxExpr = null;
    Set<String>                                     funcNames;


    public Alloy2SMTTranslator(CompModule alloyModel)
    {
        this.atom                   = "Atom";
        this.intAtom                = "IntAtom";
        this.smtProgram             = new SMTProgram();        
        this.intSort                = new IntSort();
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.atomSort               = new UninterpretedSort(this.atom);
        this.intAtomSort            = new UninterpretedSort(this.intAtom);
        this.unaryAtomSort          = new TupleSort(this.atomSort);
        this.binaryAtomSort         = new TupleSort(this.atomSort, this.atomSort);
        this.unaryIntAtomSort       = new TupleSort(this.intAtomSort);
        this.binaryIntAtomSort      = new TupleSort(this.intAtomSort, this.intAtomSort);        
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
        this.intUnivExpr            = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryIntSort);        
        this.intUniv                = new FunctionDeclaration("intUniv", setOfUnaryIntSort);
        this.intIden                = new FunctionDeclaration("intIden", setOfUnaryIntSort );
        this.intNone                = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryIntSort);
        this.valueOfIntAtom         = new FunctionDeclaration("value_of_intAtom", this.intAtomSort, this.intSort);
        this.smtProgram.addFcnDecl(this.valueOfIntAtom);
        
        this.comparisonOps          = new HashMap<>();  
        this.arithOps               = new HashMap<>();
        this.signaturesMap          = new HashMap<>();
        this.funcNamesMap           = new HashMap<>();
        this.funcDefsMap            = new HashMap<>();
        this.fieldsMap              = new HashMap<>();
        this.sigFacts               = new HashMap<>();
        this.existentialBdVars      = new ArrayList<>();
        this.funcNames              = new HashSet<>();    

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
        BoundVariableDeclaration    a       = new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr());
        BinaryExpression            memberA = new BinaryExpression(tupleA, BinaryExpression.Op.MEMBER, this.atomUniv.getConstantExpr());

        BoundVariableDeclaration    b       = new BoundVariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
        MultiArityExpression        tupleB  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,b.getConstantExpr());
        BinaryExpression            memberB = new BinaryExpression(tupleB, BinaryExpression.Op.MEMBER, this.atomUniv.getConstantExpr());

        BinaryExpression            and     = new BinaryExpression(memberA, BinaryExpression.Op.AND, memberB);

        MultiArityExpression        tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr(), b.getConstantExpr());

        BinaryExpression            member  = new BinaryExpression(tupleAB, BinaryExpression.Op.MEMBER, this.atomIden.getConstantExpr());

        BinaryExpression            equals  = new BinaryExpression(a.getConstantExpr(), BinaryExpression.Op.EQ, b.getConstantExpr());

        BinaryExpression            equiv   = new BinaryExpression(member, BinaryExpression.Op.EQ, equals);

        BinaryExpression            implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES , equiv);
        
        QuantifiedExpression        idenSemantics  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b);

        this.smtProgram.addAssertion(new Assertion("Empty unary relation definition for Atom", new BinaryExpression(this.atomNone.getConstantExpr(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Universe definition for Atom", new BinaryExpression(this.atomUniv.getConstantExpr(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Identity relation definition for Atom", idenSemantics));
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
            System.out.println("The input Alloy model does not have the assertion: " + assertion);
        }
    }    
    
    private void translateFuncsAndPreds()
    {        
        List<String> funcOrder = new ArrayList<>();
        Map<String, List<String>> dependency = new HashMap<>();
        
        for(Func func : this.alloyModel.getAllFunc()) 
        {
            funcNames.add(func.label);
        }       
        for(Func f : this.alloyModel.getAllFunc())
        {
            if(f.label.equalsIgnoreCase("this/$$Default"))
            {
                continue;
            }
            translateFunc(f);
            sortFunctionDependency(f.label, f.getBody(), dependency);
        }
                
        // Organize the order of dependency
        organizeDependency(dependency, funcOrder);
        
        for(int i = 0; i < funcOrder.size(); ++i)
        {            
            this.smtProgram.addFcnDef(this.funcDefsMap.get(this.funcNamesMap.get(funcOrder.get(i))));
        }
    }
    
    private void translateFunc(Func f)
    {        
        Sort    returnSort  = new BoolSort();        
        String  funcName    = TranslatorUtils.sanitizeName(f.label);                
        List<BoundVariableDeclaration>      bdVars          = new ArrayList<>();
        Map<String, Expression>             variablesScope  = new HashMap<>();
                
        // Save function name
        this.funcNamesMap.put(f.label, funcName);        
        // Declare input variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  bdVarName       = n.label;
                String  sanBdVarName    = TranslatorUtils.sanitizeName(n.label);
                Sort    bdVarSort       = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.decls.get(i).expr));
                BoundVariableDeclaration bdVarDecl = new BoundVariableDeclaration(sanBdVarName, bdVarSort);
                
                bdVars.add(bdVarDecl);
                variablesScope.put(bdVarName, bdVarDecl.getConstantExpr());
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
    
    
    
    
    

    /**
     * This is to sort out the function dependencies so that 
     * we can print them in the right order
     */
    private void sortFunctionDependency(String callingFuncName, Expr expr, Map<String, List<String>> dependency)
    {
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary)expr;
            switch (exprUnary.op)
            {
                case NOOP       :
                case NO         : 
                case SOME       : 
                case ONE        : 
                case LONE       : 
                case TRANSPOSE  : 
                case CLOSURE    :
                case RCLOSURE   : 
                case ONEOF      :
                case LONEOF     :
                case SOMEOF     : 
                case SETOF      :                 
                case NOT        : sortFunctionDependency(callingFuncName, exprUnary.sub, dependency); break;
                case CAST2INT   : return;
                case CAST2SIGINT : return;
                default:
                {
                    throw new UnsupportedOperationException("Not supported yet: " + exprUnary.op);
                }
            }            
        } 
        else if(expr instanceof ExprBinary)
        {
            sortFunctionDependency(callingFuncName, ((ExprBinary)expr).left, dependency);
            sortFunctionDependency(callingFuncName, ((ExprBinary)expr).right, dependency);
        }
        else if(expr instanceof ExprQt)
        {
            for (Decl decl: ((ExprQt)expr).decls)
            {
                sortFunctionDependency(callingFuncName, decl.expr, dependency);
            }            
            sortFunctionDependency(callingFuncName, ((ExprQt)expr).sub, dependency);
        }
        else if(expr instanceof ExprList)
        {
            for(Expr argExpr : ((ExprList)expr).args)
            {
                sortFunctionDependency(callingFuncName, argExpr, dependency);
            }            
        }
        else if(expr instanceof ExprCall)
        {
            for(Expr e : ((ExprCall)expr).args)
            {
                sortFunctionDependency(callingFuncName, e, dependency);
            }
            addToDependency(callingFuncName, ((ExprCall)expr).fun.label, dependency);
        }
        else if(expr instanceof ExprLet)
        {
            sortFunctionDependency(callingFuncName, ((ExprLet)expr).expr, dependency);
            sortFunctionDependency(callingFuncName, ((ExprLet)expr).sub, dependency);
        }
        else if((expr instanceof ExprConstant) || (expr instanceof Sig.Field) || (expr instanceof Sig)
                || (expr instanceof ExprVar))
        {
            return;
        }
        else 
        {
            throw new UnsupportedOperationException();
        }
    }    
    
    private void addToDependency(String key, String value, Map<String, List<String>> dependency)
    {
        if(dependency.containsKey(key))        
        {
            dependency.get(key).add(value);
        }
        else
        {
            List<String> values = new ArrayList<>();
            values.add(value);
            dependency.put(key, values);
        }
    }
    
    private void organizeDependency(Map<String, List<String>> dependency, List<String> orderedFunctions)
    {
        for(Map.Entry<String, List<String>> entry : dependency.entrySet())
        {
            for(String dFuncName : entry.getValue())
            {
                if(dependency.containsKey(dFuncName))
                {
                    organizeDependency(dFuncName, dependency, orderedFunctions);
                }
                else
                {
                    orderedFunctions.add(dFuncName);
                }
            }
            orderedFunctions.add(entry.getKey());
        }
        for(Func f : this.alloyModel.getAllFunc())
        {
            if(!orderedFunctions.contains(f.label) && !f.label.equalsIgnoreCase("this/$$Default"))
            {
                orderedFunctions.add(f.label);
            }
        }
    }
    
    private void organizeDependency(String dFuncName, Map<String, List<String>> dependency, List<String> orderedFunctions)
    {
        for(String funcName : dependency.get(dFuncName))
        {
            if(dependency.containsKey(funcName))
            {
                organizeDependency(funcName, dependency, orderedFunctions);
            }
            else
            {
                orderedFunctions.add(funcName);
            }
        }
    }
     
}
