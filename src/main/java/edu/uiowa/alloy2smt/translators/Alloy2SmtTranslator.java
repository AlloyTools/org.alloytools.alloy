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
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.mapping.MappingSignature;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Alloy2SmtTranslator
{
    public final SmtProgram smtProgram;

    final String atom               = "Atom";
    final String unaryIntAtom       = "UnaryIntTup";
    final String binaryIntAtom      = "BinaryIntTup";        
    final String ternaryIntAtom     = "TernaryIntTup";     
    
    
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
    final TupleSort                 binaryIntSort;    
    final TupleSort                 binaryAtomSort;              
    final TupleSort                 ternaryIntSort;
    final UninterpretedSort         atomSort;    
    final UninterpretedSort         unaryIntTup;    
    final UninterpretedSort         binaryIntTup; 
    final UninterpretedSort         ternaryIntTup; 
    
    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;
    final FunctionDeclaration       atomUniv;
    final UnaryExpression           intUnivExpr;
    final FunctionDeclaration       atomNone;
    final FunctionDeclaration       atomIden;
    final FunctionDeclaration       intUniv;
    final UnaryExpression           intNone;
    final FunctionDeclaration       intIden;
    final FunctionDeclaration       valueOfUnaryIntTup;  
    final FunctionDeclaration       valueOfBinaryIntTup;      
    final FunctionDeclaration       valueOfTernaryIntTup;
    
    Expression                                      auxExpr;
    Set<String>                                     funcNames;
    Map<Sig, Expr>                                  sigFacts;    
    
    Map<String, String>                             funcNamesMap;
    Map<String, List<String>>                       setCompFuncNameToInputsMap;
    Map<String, Expression>                         setCompFuncNameToDefMap;
    Map<String, BoundVariableDeclaration>           setCompFuncNameToBdVarExprMap;
    Map<Sig, FunctionDeclaration>                   signaturesMap;   
    List<BoundVariableDeclaration>                  existentialBdVars;      
    Map<String, FunctionDefinition>                 funcDefsMap;        
    Map<Sig.Field, FunctionDeclaration>             fieldsMap;     
    Map<BinaryExpression.Op, FunctionDefinition>    comparisonOps;
    Map<BinaryExpression.Op, ConstantExpression>    arithOps;  
    


    public Alloy2SmtTranslator(CompModule alloyModel)
    {               
        this.smtProgram             = new SmtProgram();
        this.intSort                = new IntSort();
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.atomSort               = new UninterpretedSort(this.atom);
        this.unaryIntTup            = new UninterpretedSort(this.unaryIntAtom);
        this.binaryIntTup           = new UninterpretedSort(this.binaryIntAtom);
        this.ternaryIntTup          = new UninterpretedSort(this.ternaryIntAtom);        
        
        this.unaryAtomSort          = new TupleSort(this.atomSort);
        this.binaryAtomSort         = new TupleSort(this.atomSort, this.atomSort);
        this.unaryIntAtomSort       = new TupleSort(this.unaryIntTup);
        this.unaryIntSort           = new TupleSort(this.intSort);
        this.binaryIntSort          = new TupleSort(this.intSort, this.intSort);        
        this.ternaryIntSort         = new TupleSort(this.intSort, this.intSort, this.intSort);
        this.setOfUnaryAtomSort     = new SetSort(this.unaryAtomSort);
        this.setOfUnaryIntSort      = new SetSort(this.unaryIntSort);
        this.setOfBinaryAtomSort    = new SetSort(this.binaryAtomSort);
        this.setOfTernaryIntSort    = new SetSort(this.ternaryIntSort);
        this.signatureTranslator    = new SignatureTranslator(this);
        this.atomUniv               = new FunctionDeclaration("atomUniv", setOfUnaryAtomSort);
        this.atomNone               = new FunctionDeclaration("atomNone", setOfUnaryAtomSort);        
        this.atomIden               = new FunctionDeclaration("atomIden", setOfBinaryAtomSort );        
        this.intUniv                = new FunctionDeclaration("intUniv", setOfUnaryIntSort);
        this.intIden                = new FunctionDeclaration("intIden", setOfUnaryIntSort );
        this.intNone                = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryIntSort);
        this.intUnivExpr            = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryIntSort);                
        this.valueOfUnaryIntTup     = new FunctionDeclaration("value_of_unaryIntTup", this.unaryIntTup, this.unaryIntSort);
        this.valueOfBinaryIntTup    = new FunctionDeclaration("value_of_binaryIntTup", this.binaryIntTup, this.binaryIntSort);        
        this.valueOfTernaryIntTup   = new FunctionDeclaration("value_of_ternaryIntTup", this.ternaryIntTup, this.ternaryIntSort);
        
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
        this.smtProgram.addSort(this.atomSort);
        this.smtProgram.addSort(this.unaryIntTup);
        this.smtProgram.addSort(this.binaryIntTup);
        this.smtProgram.addSort(this.ternaryIntTup);
        this.smtProgram.addFunctionDeclaration(this.valueOfUnaryIntTup);
        this.smtProgram.addFunctionDeclaration(this.valueOfBinaryIntTup);
        this.smtProgram.addFunctionDeclaration(this.valueOfTernaryIntTup);
        
        this.setCompFuncNameToInputsMap     = new HashMap<>();
        this.setCompFuncNameToDefMap        = new HashMap<>(); 
        this.setCompFuncNameToBdVarExprMap  = new HashMap<>();
        this.exprTranslator                 = new ExprTranslator(this);        
    }

    public SmtProgram translate(String assertion)
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
            if(!this.setCompFuncNameToDefMap.containsKey(funcOrder.get(i)))
            {
                this.smtProgram.addFunctionDefinition(this.funcDefsMap.get(this.funcNamesMap.get(funcOrder.get(i))));
            }            
        }
    }

    private void translateSetCompFunc(Func f)
    {
        String funcName = f.label;
        Map<String, Expression> variablesScope = new HashMap<>();

        ExprQt exprQtBody = (ExprQt)(((ExprUnary)f.getBody()).sub);

        List<Sort> elementSorts = new ArrayList<>();

        for(int i = 0; i < exprQtBody.decls.size(); ++i)
        {                    
            for(int j = 0; j < exprQtBody.decls.get(i).names.size(); ++j)
            {
                elementSorts.addAll(exprTranslator.getExprSorts(exprQtBody.decls.get(i).expr));
            }                    
        }

        String              setBdVarName    = TranslatorUtils.getNewSetName();
        SetSort             setSort         = new SetSort(new TupleSort(elementSorts));
        BoundVariableDeclaration setBdVar   = new BoundVariableDeclaration(setBdVarName, setSort);
        LinkedHashMap<BoundVariableDeclaration, Expression> inputBdVars = new LinkedHashMap<>();
        List<String> inputVarNames = new ArrayList<>();
        
        // Declare input variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  bdVarName       = n.label;
                String  sanBdVarName    = TranslatorUtils.sanitizeName(n.label);
                Sort    bdVarSort       = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.decls.get(i).expr));
                BoundVariableDeclaration bdVarDecl = new BoundVariableDeclaration(sanBdVarName, bdVarSort);
                
                inputVarNames.add(sanBdVarName);
                variablesScope.put(bdVarName, bdVarDecl.getConstantExpr());
            }
        }        

        for(Decl decl : exprQtBody.decls)
        {                    
            Expression declExpr         = exprTranslator.getDeclarationExpr(decl, variablesScope);
            List<Sort> declExprSorts    = exprTranslator.getExprSorts(decl.expr);

            for (ExprHasName name: decl.names)
            {
                String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                BoundVariableDeclaration bdVar = new BoundVariableDeclaration(sanitizedName, declExprSorts.get(0));
                variablesScope.put(name.label, bdVar.getConstantExpr());
                inputBdVars.put(bdVar, declExpr);                
            }                    
        }
        
        Expression setCompBodyExpr  = exprTranslator.translateExpr(exprQtBody.sub, variablesScope);
        Expression membership       = exprTranslator.getMemberExpression(inputBdVars, 0);

        for(int i = 1; i < inputBdVars.size(); ++i)
        {
            membership = new BinaryExpression(membership, BinaryExpression.Op.AND, exprTranslator.getMemberExpression(inputBdVars, i));
        }
        membership = new BinaryExpression(membership, BinaryExpression.Op.AND, setCompBodyExpr);
        Expression setMembership = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(new ArrayList<>(inputBdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getConstantExpr());
        membership = new BinaryExpression(membership, BinaryExpression.Op.EQ, setMembership);
        Expression forallExpr = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, new ArrayList<>(inputBdVars.keySet()), membership);

        this.setCompFuncNameToBdVarExprMap.put(funcName, setBdVar);
        this.setCompFuncNameToDefMap.put(funcName, forallExpr); 
        this.setCompFuncNameToInputsMap.put(funcName, inputVarNames);                       
    }    
         
    
    private void translateFunc(Func f)
    { 
        if(isSetComp(f.getBody()))
        {
           translateSetCompFunc(f);
           return; 
        }
        
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
        else if(expr instanceof ExprITE)
        {
            sortFunctionDependency(callingFuncName, ((ExprITE)expr).cond, dependency);
            sortFunctionDependency(callingFuncName, ((ExprITE)expr).left, dependency);
            sortFunctionDependency(callingFuncName, ((ExprITE)expr).right, dependency);
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
                else if(!orderedFunctions.contains(dFuncName))
                {
                    orderedFunctions.add(dFuncName);
                }
            }
            if(!orderedFunctions.contains(entry.getKey()))
            {
                orderedFunctions.add(entry.getKey());
            }            
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
            else if(!orderedFunctions.contains(funcName))             
            {
                orderedFunctions.add(funcName);
            }
        }
        if(!orderedFunctions.contains(dFuncName))
        {
            orderedFunctions.add(dFuncName);
        }         
    }
    
    
    private boolean isSetComp(Expr expr)
    {
        if(expr instanceof ExprUnary)
        {
            if(((ExprUnary)expr).op == ExprUnary.Op.NOOP) 
            {
                return (((ExprUnary)expr).sub instanceof ExprQt) && ((ExprQt)((ExprUnary)expr).sub).op == ExprQt.Op.COMPREHENSION;
            }
        }
        return false;
    }

    /**
     *
     * @return a mapper that maps signatures's names to the corresponding names
     * in the generated smt script
     */
    public Mapper generateMapper()
    {
        Mapper              mapper  = new Mapper();
        Map<Expr, Integer>  idMap   = new HashMap<>();

        // add special signatures

        MappingSignature univSignature = getSignature(idMap, Sig.UNIV);
        mapper.signatures.add(univSignature);

        //ToDo: add other special signatures: none, iden, string, int

        for (Sig sig : topLevelSigs)
        {
            mapper.signatures.addAll(getSignatures(idMap, sig));
        }

        return mapper;
    }

    private List<MappingSignature> getSignatures(Map<Expr, Integer> idMap,Sig sig) {

        List<MappingSignature> signatures = new ArrayList<>();

        MappingSignature signature = getSignature(idMap, sig);

        signatures.add(signature);

        if(sig instanceof Sig.PrimSig)
        {
            for (Sig childSig : children((Sig.PrimSig) sig))
            {
                signatures.addAll(getSignatures(idMap, childSig));
            }
        }

        return signatures;
    }

    private List<Sig> children(Sig.PrimSig sig)
    {
        if (sig == Sig.NONE)
        {
            return new ArrayList<>();
        }
        if (sig != Sig.UNIV)
        {
            List<Sig> sigs = new ArrayList<>();
            sig.children().forEach(sigs::add);
            return sigs;
        }
        else
        {
            return this.topLevelSigs;
        }
    }


    private MappingSignature getSignature(Map<Expr, Integer> idMap, Sig sig)
    {
        MappingSignature signature = new MappingSignature();

        signature.label         = sig.label;
        signature.functionName  = signaturesMap.get(sig).getName();

        signature.id            = getId(sig, idMap);

        if (sig instanceof Sig.PrimSig && sig != Sig.UNIV)
        {
            signature.parentId  = getId(((Sig.PrimSig) sig).parent, idMap);
        }

        signature.builtIn       = sig.builtin;
        signature.isAbstract    = sig.isAbstract != null;
        signature.isOne         = sig.isOne != null;
        signature.isLone        = sig.isLone != null;
        signature.isSome        = sig.isSome != null;
        signature.isPrivate     = sig.isPrivate != null;
        signature.isMeta        = sig.isMeta != null;

        if(sig instanceof Sig.SubsetSig)
        {
            signature.isExact   = ((Sig.SubsetSig) sig).exact;
        }

        signature.isEnum        = sig.isEnum != null;

        return signature;
    }

    // Sig.univ usually has id = 2 (1 ++)
    private int mappingSignatureId =  TranslatorUtils.UNIV_SIGNATURE_ID - 1;

    private int getUniqueId()
    {
        mappingSignatureId ++;
        return mappingSignatureId;
    }

    /**
     *
     * @param expr can be Sig, Field, or Skolem
     * @param idMap a store for unqiue ids
     * @return the unique id of the expr it exists in the idMap, or generate  a new id
     */
    private int getId(Expr expr, Map<Expr, Integer>  idMap)
    {
        Integer id = idMap.get(expr);

        if(id == null)
        {
            id = getUniqueId();
            idMap.put(expr, id);
        }
        return id;
    }
}
