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
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class Alloy2SmtTranslator extends AbstractTranslator
{
    final CompModule                alloyModel;
    final List<Sig>                 reachableSigs;
    final List<Sig>                 topLevelSigs;
    final List<Command>             commands;

    final SignatureTranslator       signatureTranslator;
    final ExprTranslator            exprTranslator;

    Set<String> funcNames;
    //ToDo: it is really important to remove this variable. It is the source of many bugs
    Expression                                      auxExpr;
    Map<Sig, Expr>                                  sigFacts;
    
    Map<String, String>                             funcNamesMap;
    Map<String, List<String>> setComprehensionFuncNameToInputsMap;
    Map<String, Expression>                         setCompFuncNameToDefMap;
    Map<String, VariableDeclaration>                setCompFuncNameToBdVarExprMap;
    Map<Sig, FunctionDeclaration>                   signaturesMap;   
    List<VariableDeclaration>                       existentialBdVars;
    Map<Sig.Field, FunctionDeclaration>             fieldsMap;
    Map<String, Func> nameToFuncMap;
    Map<Expr, Integer>  sigToIdMap;
    Map<Expr, FunctionDeclaration> multiplicityVariableMap;


    public Alloy2SmtTranslator(CompModule alloyModel)
    {
        TranslatorUtils.reset();

        this.smtProgram             = new SmtProgram();
        this.alloyModel             = alloyModel;
        this.reachableSigs          = new ArrayList<>();
        this.topLevelSigs           = new ArrayList<>();
        this.commands               = alloyModel.getAllCommands();

        this.signatureTranslator    = new SignatureTranslator(this);
        this.comparisonOperations = new HashMap<>();
        this.arithmeticOperations = new HashMap<>();
        this.signaturesMap          = new HashMap<>();
        this.funcNamesMap           = new HashMap<>();
        this.functionsMap           = new HashMap<>();
        this.nameToFuncMap          = new HashMap<>();
        this.fieldsMap              = new HashMap<>();
        this.sigFacts               = new HashMap<>();
        this.existentialBdVars      = new ArrayList<>();
        this.funcNames              = new HashSet<>();
        this.integerConstants       = new HashMap<>();
        this.sigToIdMap             = new HashMap<>();
        this.multiplicityVariableMap = new HashMap<>();

        this.signaturesMap.put(Sig.UNIV, atomUniverse);
        this.signaturesMap.put(Sig.SIGINT, intUniv);
        this.smtProgram.addSort(atomSort);
        this.smtProgram.addSort(uninterpretedInt);
        this.smtProgram.addFunction(uninterpretedIntValue);

        this.functionsMap.put(uninterpretedIntValue.getName(), uninterpretedIntValue);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>();
        this.setCompFuncNameToDefMap        = new HashMap<>(); 
        this.setCompFuncNameToBdVarExprMap  = new HashMap<>();
        this.exprTranslator                 = new ExprTranslator(this);        
    }

    public Alloy2SmtTranslator(Alloy2SmtTranslator translator)
    {
        this.smtProgram             = new SmtProgram(translator.smtProgram);
        this.alloyModel             = translator.alloyModel;
        this.reachableSigs          = new ArrayList<>(translator.reachableSigs);
        this.topLevelSigs           = new ArrayList<>(translator.topLevelSigs);
        this.sigToIdMap             = new HashMap<>(translator.sigToIdMap);

        this.commands               = this.alloyModel.getAllCommands();


        this.signatureTranslator    = new SignatureTranslator(this);
        this.comparisonOperations = new HashMap<>(translator.comparisonOperations);
        this.integerConstants       = new HashMap<>(translator.integerConstants);
        this.arithmeticOperations = new HashMap<>(translator.arithmeticOperations);
        this.signaturesMap          = new HashMap<>(translator.signaturesMap);
        this.funcNamesMap           = new HashMap<>(translator.funcNamesMap);
        this.functionsMap           = new HashMap<>(translator.functionsMap);
        this.fieldsMap              = new HashMap<>(translator.fieldsMap);
        this.sigFacts               = new HashMap<>(translator.sigFacts);
        this.existentialBdVars      = new ArrayList<>(translator.existentialBdVars);
        this.funcNames              = new HashSet<>(translator.funcNames);
        this.multiplicityVariableMap = new HashMap<>(translator.multiplicityVariableMap);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>(translator.setComprehensionFuncNameToInputsMap);
        this.setCompFuncNameToDefMap        = new HashMap<>(translator.setCompFuncNameToDefMap);
        this.setCompFuncNameToBdVarExprMap  = new HashMap<>(translator.setCompFuncNameToBdVarExprMap);
        this.exprTranslator                 = new ExprTranslator(this);
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

    @Override
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
        this.smtProgram.addFunction(this.atomUniverse);
        this.smtProgram.addFunction(this.atomIdentity);
        this.smtProgram.addFunction(this.intUniv);
    }

    private void translateSpecialAssertions()
    {
        // Axiom for identity relation
        VariableDeclaration a       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getVariable());
        BinaryExpression            memberA = new BinaryExpression(tupleA, BinaryExpression.Op.MEMBER, this.atomUniverse.getVariable());

        VariableDeclaration b       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort);
        MultiArityExpression        tupleB  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,b.getVariable());
        BinaryExpression            memberB = new BinaryExpression(tupleB, BinaryExpression.Op.MEMBER, this.atomUniverse.getVariable());

        BinaryExpression            and     = new BinaryExpression(memberA, BinaryExpression.Op.AND, memberB);

        MultiArityExpression        tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getVariable(), b.getVariable());

        BinaryExpression            member  = new BinaryExpression(tupleAB, BinaryExpression.Op.MEMBER, this.atomIdentity.getVariable());

        BinaryExpression            equals  = new BinaryExpression(a.getVariable(), BinaryExpression.Op.EQ, b.getVariable());

        BinaryExpression            equiv   = new BinaryExpression(member, BinaryExpression.Op.EQ, equals);

        BinaryExpression            implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES , equiv);
        
        QuantifiedExpression        idenSemantics  = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, a, b);

        this.smtProgram.addAssertion(new Assertion("Empty unary relation definition for Atom", new BinaryExpression(this.atomNone.getVariable(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.EMPTYSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Universe definition for Atom", new BinaryExpression(this.atomUniverse.getVariable(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Universe definition for UninterpretedInt", new BinaryExpression(intUniv.getVariable(), BinaryExpression.Op.EQ, new UnaryExpression(UnaryExpression.Op.UNIVSET, setOfUninterpretedIntTuple))));
        this.smtProgram.addAssertion(new Assertion("Identity relation definition for Atom", idenSemantics));

        // uninterpretedIntValue is injective function
        VariableDeclaration X = new VariableDeclaration("x", uninterpretedInt);
        VariableDeclaration Y = new VariableDeclaration("y", uninterpretedInt);
        Expression XEqualsY = new BinaryExpression(X.getVariable(), BinaryExpression.Op.EQ, Y.getVariable());
        Expression notXEqualsY = new UnaryExpression(UnaryExpression.Op.NOT, XEqualsY);

        Expression XValue = new FunctionCallExpression(uninterpretedIntValue, X.getVariable());
        Expression YValue = new FunctionCallExpression(uninterpretedIntValue, Y.getVariable());

        Expression XValueEqualsYValue = new BinaryExpression(XValue, BinaryExpression.Op.EQ, YValue);
        Expression notXValueEqualsYValue = new UnaryExpression(UnaryExpression.Op.NOT, XValueEqualsYValue);
        Expression implication = new BinaryExpression(notXEqualsY, BinaryExpression.Op.IMPLIES, notXValueEqualsYValue);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implication, X, Y);

        smtProgram.addAssertion(new Assertion(uninterpretedIntValueName + " is injective", forAll));

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
            if (module.getModelName().equals("util/integer"))
            {
                continue;
            }
            for (Func func : module.getAllFunc())
            {
                funcNames.add(func.label);
                this.nameToFuncMap.put(func.label, func);
                sortFunctionDependency(func.label, func.getBody(), dependency);
            }
        }

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
                elementSorts.addAll(AlloyUtils.getExprSorts(exprQtBody.decls.get(i).expr));
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
                variablesScope.put(bdVarName, bdVarDecl.getVariable());
            }
        }        

        for(Decl decl : exprQtBody.decls)
        {                    
            Expression declExpr         = exprTranslator.translateExpr(decl.expr, variablesScope);
            List<Sort> declExprSorts    = AlloyUtils.getExprSorts(decl.expr);

            for (ExprHasName name: decl.names)
            {
                String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                VariableDeclaration bdVar = new VariableDeclaration(sanitizedName, declExprSorts.get(0));
                variablesScope.put(name.label, bdVar.getVariable());
                inputBdVars.put(bdVar, declExpr);                
            }                    
        }
        
        Expression setCompBodyExpr  = exprTranslator.translateExpr(exprQtBody.sub, variablesScope);
        Expression membership       = AlloyUtils.getMemberExpression(inputBdVars, 0);

        for(int i = 1; i < inputBdVars.size(); ++i)
        {
            membership = new BinaryExpression(membership, BinaryExpression.Op.AND, AlloyUtils.getMemberExpression(inputBdVars, i));
        }
        membership = new BinaryExpression(membership, BinaryExpression.Op.AND, setCompBodyExpr);
        Expression setMembership = new BinaryExpression(exprTranslator.exprUnaryTranslator.mkTupleExpr(new ArrayList<>(inputBdVars.keySet())), BinaryExpression.Op.MEMBER, setBdVar.getVariable());
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
                variablesScope.put(bdVarName, bdVarDecl.getVariable());
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
                case CARDINALITY:
                case NOT        : sortFunctionDependency(callingFuncName, exprUnary.sub, dependency); break;
                case CAST2INT   :
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
        // add special signatures

        MappingSignature univSignature = getSignature(Sig.UNIV);
        mapper.signatures.add(univSignature);

        MappingSignature intSignature = getSignature(Sig.SIGINT);
        mapper.signatures.add(intSignature);

        //ToDo: add other special signatures: none, iden, string

        for (Sig sig : topLevelSigs)
        {
            mapper.signatures.addAll(getSignatures(sig));
        }

        // add remaining signatures like int signatures
        for (Sig sig : reachableSigs)
        {
            if(! sigToIdMap.keySet().contains(sig))
            {
                mapper.signatures.addAll(getSignatures(sig));
            }
        }

        for (Sig sig : reachableSigs)
        {
            mapper.fields.addAll(getFields(sig));
        }

        return mapper;
    }

    private List<MappingSignature> getSignatures(Sig sig)
    {
        List<MappingSignature> signatures = new ArrayList<>();
        MappingSignature signature = getSignature(sig);
        signatures.add(signature);

        for (Sig childSig : children(sig))
        {
            signatures.addAll(getSignatures(childSig));
        }

        return signatures;
    }

    private List<MappingField> getFields(Sig sig)
    {
        List<MappingField> fields = new ArrayList<>();

        for (Sig.Field field : sig.getFields())
        {
            fields.add(getField(field));
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


    private MappingSignature getSignature(Sig sig)
    {
        MappingSignature signature = new MappingSignature();

        signature.label         = sig.label;
        signature.functionName  = signaturesMap.get(sig).getName();

        signature.id            = getSigId(sig);

        // find the ids of the parents
        if (sig instanceof Sig.PrimSig && sig != Sig.UNIV)
        {
            signature.parents.add(getSigId(((Sig.PrimSig) sig).parent));
        }
        else if (sig instanceof Sig.SubsetSig)
        {
            signature.isSubset = true;
            for (Sig parent :  ((Sig.SubsetSig) sig).parents)
            {
                signature.parents.add(getSigId(parent));
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

    private MappingField getField(Sig.Field field)
    {
        MappingField mappingField   = new MappingField();

        mappingField.label          = field.label;
        mappingField.functionName   = fieldsMap.get(field).getName();
        mappingField.id             = getSigId(field);
        mappingField.parentId       = getSigId(field.sig);
        mappingField.isPrivate      = field.isPrivate != null;
        mappingField.isMeta         = field.isMeta != null;
        mappingField.types          = getFieldTypes(field);

        return mappingField;
    }

    private List<List<MappingType>> getFieldTypes(Sig.Field field)
    {
        List<List<MappingType>> types = new ArrayList<>();
        for(List<Sig.PrimSig> sigs: field.type().fold())
        {
            List<MappingType> type = new ArrayList<>();
            for (Sig sig: sigs)
            {
                MappingType mappingType = new MappingType();
                mappingType.id = getSigId(sig);
                type.add(mappingType);
            }
            types.add(type);
        }
        return types;
    }

    // Sig.univ usually has id = 2 (1 ++)
    private int mappingSignatureId = 1;

    private int getUniqueId()
    {
        mappingSignatureId ++;
        return mappingSignatureId;
    }

    /**
     *
     * @param expr can be Sig, Field, or Skolem
     * @return the unique id of the expr it exists in the idMap, or generate  a new id
     */
    public int getSigId(Expr expr)
    {
        Integer id = sigToIdMap.get(expr);

        if(id == null)
        {
            id = getUniqueId();
            sigToIdMap.put(expr, id);
        }
        return id;
    }

    /**
     * @param commandIndex the index of the run command
     * @return an assertion that represents the translation
     * of the command
     */
    public Assertion translateCommand(int commandIndex, boolean includeScope)
    {
        Command command = this.commands.get(commandIndex);

        Expression expression = this.exprTranslator.translateExpr(command.formula);

        if(includeScope)
        {
            for (Sig signature: reachableSigs)
            {
                if (signature instanceof Sig.PrimSig)
                {
                    Optional<CommandScope> optional = command.scope
                            .stream()
                            .filter(s -> s.sig == signature)
                            .findFirst();
                    int scope;
                    BinaryExpression.Op op;
                    if (optional.isPresent())
                    {
                        CommandScope commandScope = optional.get();
                        if(commandScope.isExact)
                        {
                            op = BinaryExpression.Op.EQ;
                        }
                        else
                        {
                            op = BinaryExpression.Op.SUBSET;
                        }
                        scope = commandScope.endingScope;
                    }
                    else
                    {
                        op = BinaryExpression.Op.SUBSET;
                        if(signature.isAbstract == null)
                        {
                            scope = command.overall;
                        }
                        else
                        {
                            // the scope is the sum of its children
                            scope = getScope((Sig.PrimSig) signature, command);
                        }
                    }

                    Expression variable = signaturesMap.get(signature).getVariable();
                    if(scope >= 1)
                    {
                        List<VariableDeclaration> declarations = new ArrayList<>();
                        Sort sort = signature.type().is_int()? AbstractTranslator.uninterpretedInt: AbstractTranslator.atomSort;
                        VariableDeclaration firstAtom = new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort);
                        declarations.add(firstAtom);
                        Expression firstTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getVariable());
                        Expression set = new UnaryExpression(UnaryExpression.Op.SINGLETON, firstTuple);
                        for (int i = 1; i < scope; i++)
                        {
                            VariableDeclaration declaration = new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort);
                            declarations.add(declaration);
                            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, declaration.getVariable());
                            Expression singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
                            set = new BinaryExpression(singleton, BinaryExpression.Op.UNION, set);
                        }

                        Expression constraint = new BinaryExpression(variable, op, set);
                        if(declarations.size() > 1)
                        {
                            List<Expression> expressions = declarations
                                    .stream().map(d -> d.getVariable())
                                    .collect(Collectors.toList());
                            Expression distinct = new MultiArityExpression(MultiArityExpression.Op.DISTINCT, expressions);
                            constraint = new BinaryExpression(constraint, BinaryExpression.Op.AND, distinct);
                        }
                        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, declarations, constraint);
                        expression = new BinaryExpression(expression, BinaryExpression.Op.AND, exists);
                    }
                }
            }
        }

        Assertion assertion = new Assertion(command.label, expression);
        return assertion;
    }

    private int getScope(Sig.PrimSig parent, Command command)
    {
        int scopeSum = 0;
        for (Sig signature: parent.children())
        {
            if(signature.isAbstract == null)
            {
                Optional<CommandScope> optional = command.scope
                        .stream()
                        .filter(s -> s.sig == signature)
                        .findFirst();
                if (optional.isPresent())
                {
                    CommandScope commandScope = optional.get();
                    scopeSum += commandScope.endingScope;
                }
                else
                {
                    scopeSum += command.overall;
                }
            }
            else
            {
                scopeSum += getScope((Sig.PrimSig) signature, command);
            }
        }

        if(scopeSum == 0) // no children yet
        {
            scopeSum = command.overall;
        }
        return scopeSum;
    }
}
