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
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class Alloy2SmtTranslator extends AbstractTranslator
{
    private final static int        DefaultScope = 3;
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
        VariableDeclaration a       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort, null);
        MultiArityExpression        tupleA  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getVariable());
        BinaryExpression            memberA = BinaryExpression.Op.MEMBER.make(tupleA, this.atomUniverse.getVariable());

        VariableDeclaration b       = new VariableDeclaration(TranslatorUtils.getNewAtomName(), atomSort, null);
        MultiArityExpression        tupleB  = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,b.getVariable());
        BinaryExpression            memberB = BinaryExpression.Op.MEMBER.make(tupleB, this.atomUniverse.getVariable());

        BinaryExpression            and     = BinaryExpression.Op.AND.make(memberA, memberB);

        MultiArityExpression        tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE,a.getVariable(), b.getVariable());

        BinaryExpression            member  = BinaryExpression.Op.MEMBER.make(tupleAB, this.atomIdentity.getVariable());

        BinaryExpression            equals  = BinaryExpression.Op.EQ.make(a.getVariable(), b.getVariable());

        BinaryExpression            equiv   = BinaryExpression.Op.EQ.make(member, equals);

        BinaryExpression            implies = BinaryExpression.Op.IMPLIES.make(and, equiv);
        
        QuantifiedExpression        idenSemantics  = QuantifiedExpression.Op.FORALL.make(implies, a, b);

        this.smtProgram.addAssertion(new Assertion("Empty unary relation definition for Atom", BinaryExpression.Op.EQ.make(this.atomNone.getVariable(), UnaryExpression.Op.EMPTYSET.make(setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Universe definition for Atom", BinaryExpression.Op.EQ.make(this.atomUniverse.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUnaryAtomSort))));
        this.smtProgram.addAssertion(new Assertion("Universe definition for UninterpretedInt", BinaryExpression.Op.EQ.make(intUniv.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUninterpretedIntTuple))));
        this.smtProgram.addAssertion(new Assertion("Identity relation definition for Atom", idenSemantics));

        // uninterpretedIntValue is injective function
        VariableDeclaration X = new VariableDeclaration("x", uninterpretedInt, null);
        VariableDeclaration Y = new VariableDeclaration("y", uninterpretedInt, null);
        Expression XEqualsY = BinaryExpression.Op.EQ.make(X.getVariable(), Y.getVariable());
        Expression notXEqualsY = UnaryExpression.Op.NOT.make(XEqualsY);

        Expression XValue = new FunctionCallExpression(uninterpretedIntValue, X.getVariable());
        Expression YValue = new FunctionCallExpression(uninterpretedIntValue, Y.getVariable());

        Expression XValueEqualsYValue = BinaryExpression.Op.EQ.make(XValue, YValue);
        Expression notXValueEqualsYValue = UnaryExpression.Op.NOT.make(XValueEqualsYValue);
        Expression implication = BinaryExpression.Op.IMPLIES.make(notXEqualsY, notXValueEqualsYValue);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implication, X, Y);

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
        //ToDo: refactor this function to use ExprQtTranslator
        String funcName = f.label;
        Environment environment = new Environment();

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
        VariableDeclaration setBdVar   = new VariableDeclaration(setBdVarName, setSort, null);
        LinkedHashMap<VariableDeclaration, Expression> inputBdVars = new LinkedHashMap<>();
        List<String> inputVarNames = new ArrayList<>();
        
        // Declare input variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  variableName       = n.label;
                Sort    bdVarSort       = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.decls.get(i).expr));
                VariableDeclaration bdVarDecl = new VariableDeclaration(variableName, bdVarSort, null);
                
                inputVarNames.add(variableName);
                environment.put(variableName, bdVarDecl.getVariable());
            }
        }        

        for(Decl decl : exprQtBody.decls)
        {                    
            Expression declExpr         = exprTranslator.translateExpr(decl.expr, environment);
            List<Sort> declExprSorts    = AlloyUtils.getExprSorts(decl.expr);

            for (ExprHasName name: decl.names)
            {
                String label = name.label;
                VariableDeclaration bdVar = new VariableDeclaration(label, declExprSorts.get(0), null);
                environment.put(name.label, bdVar.getVariable());
                inputBdVars.put(bdVar, declExpr);                
            }                    
        }
        
        Expression setCompBodyExpr  = exprTranslator.translateExpr(exprQtBody.sub, environment);
        Expression membership       = AlloyUtils.getMemberExpression(inputBdVars, 0);

        for(int i = 1; i < inputBdVars.size(); ++i)
        {
            membership = BinaryExpression.Op.AND.make(membership, AlloyUtils.getMemberExpression(inputBdVars, i));
        }
        membership = BinaryExpression.Op.AND.make(membership, setCompBodyExpr);
        Expression setMembership = BinaryExpression.Op.MEMBER.make(exprTranslator.exprUnaryTranslator.mkTupleExpr(new ArrayList<>(inputBdVars.keySet())), setBdVar.getVariable());
        membership = BinaryExpression.Op.EQ.make(membership, setMembership);
        Expression forallExpr = QuantifiedExpression.Op.FORALL.make(membership, new ArrayList<>(inputBdVars.keySet()));

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

        Sort returnSort = BoolSort.getInstance();
        String functionName = f.label;
        List<VariableDeclaration> arguments = new ArrayList<>();
        Environment environment = new Environment();
                
        // Save function name
        this.funcNamesMap.put(f.label, functionName);
        // Declare argument variables
        for(int i = 0; i < f.decls.size(); ++i)
        {
            for(ExprHasName n : f.decls.get(i).names)
            {
                String  label = n.label;
                Expression range = this.exprTranslator.translateExpr(f.decls.get(i).expr);
                VariableDeclaration argument = new VariableDeclaration(label, range.getSort(), null);
                Expression subset = BinaryExpression.Op.SUBSET.make(argument.getVariable(), range);
                argument.setConstraint(subset);
                arguments.add(argument);
                environment.put(label, argument.getVariable());
            }
        }
        // If the function is not predicate, we change its returned type.
        if(!f.isPred)
        {
            returnSort = TranslatorUtils.getSetSortOfAtomWithArity(getArityofExpr(f.returnDecl));
        }
        
        FunctionDefinition funcDef = new FunctionDefinition(functionName, arguments, returnSort,
                                                            this.exprTranslator.translateExpr(f.getBody(), environment));
        this.functionsMap.put(functionName, funcDef);
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
        this.smtProgram.addAssertion(new Assertion(assertionName, UnaryExpression.Op.NOT.make(expression)));
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
        signature.functionName  = TranslatorUtils.getOriginalName(signaturesMap.get(sig).getName());

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
        mappingField.functionName   = TranslatorUtils.getOriginalName(fieldsMap.get(field).getName());
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
            Map<Sig, Map<Sig, Integer>> childrenScope = new HashMap<>();
            for (Sig signature: reachableSigs)
            {
                if (signature instanceof Sig.PrimSig)
                {
                    Optional<CommandScope> optional = command.scope
                            .stream()
                            .filter(s -> s.sig == signature)
                            .findFirst();
                    int scope = 0;
                    BinaryExpression.Op op;
                    if (optional.isPresent())
                    {
                        CommandScope commandScope = optional.get();
                        if(commandScope.isExact || alloyModel.getExactSigs().contains(signature))
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
                        if(alloyModel.getExactSigs().contains(signature))
                        {
                            op = BinaryExpression.Op.EQ;
                        }
                        else
                        {
                            op = BinaryExpression.Op.SUBSET;
                        }

                        if(signature.isTopLevel())
                        {
                            if(signature.isAbstract == null)
                            {
                                // no scope specification is given, default value is used
                                scope = command.overall == -1 ? Alloy2SmtTranslator.DefaultScope: command.overall;
                            }
                            else
                            {
                                childrenScope.put(signature, new HashMap<>());
                                // the scope is the sum of its children
                                scope = getScope((Sig.PrimSig) signature, command, childrenScope);
                            }
                        }
                        else
                        {
                            // the signature has no implicit bound
                        }
                    }

                    Expression variable = signaturesMap.get(signature).getVariable();

                    if(scope >= 1)
                    {
                        List<VariableDeclaration> declarations = new ArrayList<>();
                        Sort sort = signature.type().is_int()? AbstractTranslator.uninterpretedInt: AbstractTranslator.atomSort;
                        VariableDeclaration firstAtom = new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort, null);
                        declarations.add(firstAtom);
                        Expression firstTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getVariable());
                        Expression set = UnaryExpression.Op.SINGLETON.make(firstTuple);
                        for (int i = 1; i < scope; i++)
                        {
                            VariableDeclaration declaration = new VariableDeclaration(TranslatorUtils.getNewAtomName(), sort, null);
                            declarations.add(declaration);
                            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, declaration.getVariable());
                            Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple);
                            set = BinaryExpression.Op.UNION.make(singleton, set);
                        }

                        Expression constraint = op.make(variable, set);
                        if(declarations.size() > 1)
                        {
                            List<Expression> expressions = declarations
                                    .stream().map(d -> d.getVariable())
                                    .collect(Collectors.toList());
                            Expression distinct = MultiArityExpression.Op.DISTINCT.make(expressions);
                            constraint = BinaryExpression.Op.AND.make(constraint, distinct);
                        }
                        Expression exists = QuantifiedExpression.Op.EXISTS.make(constraint, declarations);
                        expression = BinaryExpression.Op.AND.make(expression, exists);
                    }
                }
            }
        }

        Assertion assertion = new Assertion(command.toString(), expression);
        return assertion;
    }

    private int getScope(Sig.PrimSig parent, Command command,
                         Map<Sig, Map<Sig, Integer>> childrenScope)
    {
        int scopeSum = 0;
        Map<Sig, Integer> parentMap = childrenScope.get(parent);
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
                    parentMap.put(signature, commandScope.endingScope);
                }
                else
                {
                    if(signature.isOne != null)
                    {
                        scopeSum += 1;
                    }
                    else
                    {
                        // for some reason, the default scope is not used here
                        scopeSum += 0;
                    }
                }
            }
            else
            {
                childrenScope.put(signature, new HashMap<>());
                int scope = getScope((Sig.PrimSig) signature, command, childrenScope);
                parentMap.put(signature, scope);
                scopeSum += scope;
            }
        }

        if(scopeSum == 0) // no explicit scope for children is given
        {
            scopeSum = command.overall == -1 ? Alloy2SmtTranslator.DefaultScope: command.overall;
        }
        return scopeSum;
    }
}
