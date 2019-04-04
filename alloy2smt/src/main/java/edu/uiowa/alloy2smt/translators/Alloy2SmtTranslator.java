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
import edu.uiowa.alloy2smt.mapping.MappingField;
import edu.uiowa.alloy2smt.mapping.MappingSignature;
import edu.uiowa.alloy2smt.mapping.MappingType;
import edu.uiowa.alloy2smt.smtAst.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class Alloy2SmtTranslator
{
    public final SmtProgram smtProgram;

    public final static String intSortName          = "Int";
    public final static String atom                 = "Atom";
    public final static String uninterpretedIntName = "UninterpretedInt";

    final CompModule                alloyModel;
    final List<Sig>                 reachableSigs;
    final List<Sig>                 topLevelSigs;
    final List<Command>             commands;

    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;

    public final static IntSort intSort        = IntSort.getInstance();

    public final static BoolSort          boolSort               = BoolSort.getInstance();
    public final static UninterpretedSort atomSort               = new UninterpretedSort(atom);
    public final static UninterpretedSort uninterpretedInt = new UninterpretedSort(uninterpretedIntName);

    public final static TupleSort unaryAtomSort          = new TupleSort(atomSort);
    public final static TupleSort binaryAtomSort         = new TupleSort(atomSort,atomSort);
    public final static TupleSort unaryIntSort           = new TupleSort(intSort);
    public final static TupleSort ternaryIntSort         = new TupleSort(intSort,intSort,intSort);
    public final static SetSort setOfUnaryAtomSort     = new SetSort(unaryAtomSort);
    public final static SetSort setOfUnaryIntSort      = new SetSort(unaryIntSort);
    public final static SetSort setOfBinaryAtomSort    = new SetSort(binaryAtomSort);
    public final static SetSort setOfTernaryIntSort    = new SetSort(ternaryIntSort);

    public final static FunctionDeclaration atomUniv               = new FunctionDeclaration("atomUniv", setOfUnaryAtomSort);
    public final static FunctionDeclaration atomNone               = new FunctionDeclaration("atomNone", setOfUnaryAtomSort);
    public final static FunctionDeclaration atomIden               = new FunctionDeclaration("atomIden", setOfBinaryAtomSort );
    public final static FunctionDeclaration intUniv                = new FunctionDeclaration("intUniv", setOfUnaryIntSort);
    public final static FunctionDeclaration intIden                = new FunctionDeclaration("intIden", setOfUnaryIntSort );
    public final static UnaryExpression intNone                = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryIntSort);
    public final static UnaryExpression intUnivExpr            = new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryIntSort);
    public final static FunctionDeclaration valueOfUnaryIntTup     = new FunctionDeclaration("value_of_unaryIntTup", uninterpretedInt,unaryIntSort);


    Expression                                      auxExpr;
    Set<String>                                     funcNames;
    Map<Sig, Expr>                                  sigFacts;    
    
    Map<String, String>                             funcNamesMap;
    Map<String, List<String>> setComprehensionFuncNameToInputsMap;
    Map<String, Expression>                         setCompFuncNameToDefMap;
    Map<String, VariableDeclaration>                setCompFuncNameToBdVarExprMap;
    Map<Sig, FunctionDeclaration>                   signaturesMap;   
    List<VariableDeclaration>                       existentialBdVars;
    Map<String, FunctionDeclaration>                functionsMap;
    Map<Sig.Field, FunctionDeclaration>             fieldsMap;     
    Map<BinaryExpression.Op, FunctionDefinition>    comparisonOps;
    Map<BinaryExpression.Op, ConstantExpression>    arithOps;
    Map<String, Func> nameToFuncMap;


    public Alloy2SmtTranslator(CompModule alloyModel)
    {
        TranslatorUtils.reset();

        this.smtProgram             = new SmtProgram();
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.commands               = alloyModel.getAllCommands();

        this.signatureTranslator    = new SignatureTranslator(this);
        this.comparisonOps          = new HashMap<>();  
        this.arithOps               = new HashMap<>();
        this.signaturesMap          = new HashMap<>();
        this.funcNamesMap           = new HashMap<>();
        this.functionsMap           = new HashMap<>();
        this.nameToFuncMap          = new HashMap<>();
        this.fieldsMap              = new HashMap<>();
        this.sigFacts               = new HashMap<>();
        this.existentialBdVars      = new ArrayList<>();
        this.funcNames              = new HashSet<>();    

        this.signaturesMap.put(Sig.UNIV, atomUniv);
        this.signaturesMap.put(Sig.SIGINT, intUniv);
        this.smtProgram.addSort(atomSort);
        this.smtProgram.addSort(uninterpretedInt);
        this.smtProgram.addFunction(valueOfUnaryIntTup);

        this.functionsMap.put(valueOfUnaryIntTup.getName(), valueOfUnaryIntTup);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>();
        this.setCompFuncNameToDefMap        = new HashMap<>(); 
        this.setCompFuncNameToBdVarExprMap  = new HashMap<>();
        this.exprTranslator                 = new ExprTranslator(this);        
    }

    public Alloy2SmtTranslator(Alloy2SmtTranslator translator)
    {
        this.smtProgram             = new SmtProgram(translator.smtProgram);
        this.alloyModel             = translator.alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.reachableSigs.addAll(translator.reachableSigs);
        this.topLevelSigs           = new ArrayList<>();
        this.topLevelSigs.addAll(translator.topLevelSigs);

        this.commands               = this.alloyModel.getAllCommands();


        this.signatureTranslator    = new SignatureTranslator(this);
        this.comparisonOps          = new HashMap<>();
        this.comparisonOps.putAll(translator.comparisonOps);
        this.arithOps               = new HashMap<>();
        this.arithOps.putAll(translator.arithOps);
        this.signaturesMap          = new HashMap<>();
        this.signaturesMap.putAll(translator.signaturesMap);
        this.funcNamesMap           = new HashMap<>();
        this.funcNamesMap.putAll(translator.funcNamesMap);
        this.functionsMap = new HashMap<>();
        this.functionsMap.putAll(translator.functionsMap);
        this.fieldsMap              = new HashMap<>();
        this.fieldsMap.putAll(translator.fieldsMap);
        this.sigFacts               = new HashMap<>();
        this.sigFacts.putAll(translator.sigFacts);
        this.existentialBdVars      = new ArrayList<>();
        this.existentialBdVars.addAll(translator.existentialBdVars);
        this.funcNames              = new HashSet<>();
        this.funcNames.addAll(translator.funcNames);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>();
        this.setComprehensionFuncNameToInputsMap.putAll(translator.setComprehensionFuncNameToInputsMap);
        this.setCompFuncNameToDefMap        = new HashMap<>();
        this.setCompFuncNameToDefMap.putAll(translator.setCompFuncNameToDefMap);
        this.setCompFuncNameToBdVarExprMap  = new HashMap<>();
        this.setCompFuncNameToBdVarExprMap.putAll(translator.setCompFuncNameToBdVarExprMap);
        this.exprTranslator                 = new ExprTranslator(this);
    }


    void addFunction(FunctionDeclaration function)
    {
        this.functionsMap.put(function.getName(), function);
        this.smtProgram.addFunction(function);
    }

    FunctionDeclaration getFunctionFromAlloyName(String name)
    {
        FunctionDeclaration function = functionsMap.get(funcNamesMap.get(name));
        if(function == null)
        {
            throw new RuntimeException("Function " + name + " is not found.");
        }
        return function;
    }

    FunctionDeclaration getFunction(String functionName)
    {
        FunctionDeclaration function = functionsMap.get(functionName);
        if(function == null)
        {
            throw new RuntimeException("Function " + functionName + " is not found.");
        }
        return function;
    }

    public SmtProgram translate()
    {
        translateSpecialFunctions();
        this.signatureTranslator.translateSigs();
        this.signatureTranslator.translateSpecialSigFacts();
        translateFunctionsAndPredicates();
        this.signatureTranslator.translateSigFacts();
        translateFacts();
        translateSpecialAssertions();
        return this.smtProgram;
    }

    private void translateSpecialFunctions()
    {
        this.smtProgram.addFunction(this.atomNone);
        this.smtProgram.addFunction(this.atomUniv);
        this.smtProgram.addFunction(this.atomIden);
    }

    private void translateSpecialAssertions()
    {
        // Axiom for identity relation
        VariableDeclaration a       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getConstantExpr());
        BinaryExpression            memberA = new BinaryExpression(tupleA, BinaryExpression.Op.MEMBER, this.atomUniv.getConstantExpr());

        VariableDeclaration b       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
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

    private void translateFunctionsAndPredicates()
    {        
        List<String> funcOrder = new ArrayList<>();
        Map<String, List<String>> dependency = new HashMap<>();

        for (CompModule module: this.alloyModel.getAllReachableModules())
        {
            //ToDo: review the case of integer and % (mod) operator
            if(module.getModelName().equals("util/integer"))
            {
                continue;
            }
            for (Func func : module.getAllFunc())
            {
                funcNames.add(func.label);
                this.nameToFuncMap.put(func.label, func);
            }

            // translate functions in ordering module differently
            // these functions are defined in SignatureTranslator.java
            if(module.getModelName().equals("util/ordering"))
            {
                continue;
            }

            for (Func f : module.getAllFunc())
            {
                //ignore  private functions like $$Default and run$1 etc
                // run functions are handled in commands translation
                if (f.isPrivate != null)
                {
                    continue;
                }

                if(isSetComprehension(f.getBody()))
                {
                    translateSetComprehensionFunction(f);
                }
                else
                {
                    translateFunction(f);
                }
                sortFunctionDependency(f.label, f.getBody(), dependency);
            }
        }
                
        // Organize the order of dependency
        organizeDependency(dependency, funcOrder);
        
        for(int i = 0; i < funcOrder.size(); ++i)
        {
            if(!this.setCompFuncNameToDefMap.containsKey(funcOrder.get(i)))
            {
                this.smtProgram.addFunction(this.functionsMap.get(this.funcNamesMap.get(funcOrder.get(i))));
            }            
        }
    }

    private void translateSetComprehensionFunction(Func f)
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
        VariableDeclaration setBdVar   = new VariableDeclaration(setBdVarName, setSort);
        LinkedHashMap<VariableDeclaration, Expression> inputBdVars = new LinkedHashMap<>();
        List<String> inputVarNames = new ArrayList<>();
        
        // Declare input variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  bdVarName       = n.label;
                String  sanBdVarName    = TranslatorUtils.sanitizeName(n.label);
                Sort    bdVarSort       = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.decls.get(i).expr));
                VariableDeclaration bdVarDecl = new VariableDeclaration(sanBdVarName, bdVarSort);
                
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
                VariableDeclaration bdVar = new VariableDeclaration(sanitizedName, declExprSorts.get(0));
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
        this.setComprehensionFuncNameToInputsMap.put(funcName, inputVarNames);
    }    
         
    
    public FunctionDefinition translateFunction(Func f)
    {
        if(f == null)
        {
            //ToDo: fix the null issue with  examples/case_studies/firewire.als
            throw new RuntimeException("Null argument");
        }
        if(isSetComprehension(f.getBody()))
        {
           throw new RuntimeException("The body of function " + f.label + " is a set comprehension. It should be translated using method Alloy2SmtTranslator.translateSetComprehensionFunction");
        }

        Sort    returnSort  = BoolSort.getInstance();
        String  funcName    = TranslatorUtils.sanitizeName(f.label);                
        List<VariableDeclaration>      bdVars          = new ArrayList<>();
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
                VariableDeclaration bdVarDecl = new VariableDeclaration(sanBdVarName, bdVarSort);
                
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
        this.functionsMap.put(funcName, funcDef);
        return funcDef;
    }    
    
    private int getArityofExpr(Expr expr)
    {
        return expr.type().arity();    
    }

    private void translateFact(String factName, Expr factExpr)
    {
        this.smtProgram.addAssertion(new Assertion(factName, this.exprTranslator.translateExpr(factExpr)));
    }

    private void translateAssertion(String assertionName, Expr assertionExpr)
    {
        Expression expression = this.exprTranslator.translateExpr(assertionExpr);
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
        for (CompModule module: this.alloyModel.getAllReachableModules())
        {
            for (Func f : module.getAllFunc())
            {
                if (!orderedFunctions.contains(f.label) && f.isPrivate == null)
                {
                    orderedFunctions.add(f.label);
                }
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
    
    
    private boolean isSetComprehension(Expr expr)
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

        MappingSignature intSignature = getSignature(idMap, Sig.SIGINT);
        mapper.signatures.add(intSignature);

        //ToDo: add other special signatures: none, iden, string

        for (Sig sig : topLevelSigs)
        {
            mapper.signatures.addAll(getSignatures(idMap, sig));
        }

        // add remaining signatures like int signatures
        for (Sig sig : reachableSigs)
        {
            if(! idMap.keySet().contains(sig))
            {
                mapper.signatures.addAll(getSignatures(idMap, sig));
            }
        }

        for (Sig sig : reachableSigs)
        {
            mapper.fields.addAll(getFields(idMap, sig));
        }

        return mapper;
    }

    private List<MappingSignature> getSignatures(Map<Expr, Integer> idMap,Sig sig) {

        List<MappingSignature> signatures = new ArrayList<>();

        MappingSignature signature = getSignature(idMap, sig);

        signatures.add(signature);

        for (Sig childSig : children(sig))
        {
            signatures.addAll(getSignatures(idMap, childSig));
        }

        return signatures;
    }

    private List<MappingField> getFields(Map<Expr, Integer> idMap, Sig sig)
    {
        List<MappingField> fields = new ArrayList<>();

        for (Sig.Field field : sig.getFields())
        {
            fields.add(getField(idMap, field));
        }

        return fields;
    }

    private List<Sig> children(Sig sig)
    {
        if (sig == Sig.NONE)
        {
            return new ArrayList<>();
        }
        if (sig instanceof Sig.PrimSig)
        {
            List<Sig> sigs = new ArrayList<>();
            ((Sig.PrimSig) sig).children().forEach(sigs::add);
            return sigs;
        }
        return new ArrayList<>();
    }


    private MappingSignature getSignature(Map<Expr, Integer> idMap, Sig sig)
    {
        MappingSignature signature = new MappingSignature();

        signature.label         = sig.label;
        signature.functionName  = signaturesMap.get(sig).getName();

        signature.id            = getId(sig, idMap);

        // find the ids of the parents
        if (sig instanceof Sig.PrimSig && sig != Sig.UNIV)
        {
            signature.parents.add(getId(((Sig.PrimSig) sig).parent, idMap));
        }
        else if (sig instanceof Sig.SubsetSig)
        {
            signature.isSubset = true;
            for (Sig parent :  ((Sig.SubsetSig) sig).parents)
            {
                signature.parents.add(getId(parent, idMap));
            }
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

    private MappingField getField(Map<Expr,Integer> idMap, Sig.Field field)
    {
        MappingField mappingField   = new MappingField();

        mappingField.label          = field.label;
        mappingField.functionName   = fieldsMap.get(field).getName();
        mappingField.id             = getId(field, idMap);
        mappingField.parentId       = getId(field.sig, idMap);
        mappingField.isPrivate      = field.isPrivate != null;
        mappingField.isMeta         = field.isMeta != null;
        mappingField.types          = getFieldType(idMap, field);

        return mappingField;
    }

    private List<MappingType> getFieldType(Map<Expr,Integer> idMap, Sig.Field field)
    {
        List<MappingType> types = new ArrayList<>(field.type().arity());

        List<Sig> sigs          = field.type().fold().stream()
                .flatMap(s -> s.stream()).collect(Collectors.toList());

        for (Sig sig : sigs)
        {
            MappingType mappingType = new MappingType();
            mappingType.id          = getId(sig, idMap);
            types.add(mappingType);
        }

        return types;
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

    /**
     * @param commandIndex the index of the run command
     * @return an assertion that represents the translation
     * of the command
     */
    public Assertion translateCommand(int commandIndex)
    {
        Command command = this.commands.get(commandIndex);

        Expression expression = this.exprTranslator.translateExpr(command.formula);

        Assertion assertion = new Assertion(command.label, expression);

        return assertion;
    }
}
