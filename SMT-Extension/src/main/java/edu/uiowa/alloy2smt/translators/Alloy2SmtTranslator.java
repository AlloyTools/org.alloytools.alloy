/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.mapping.Mapper;
import edu.uiowa.alloy2smt.mapping.MappingField;
import edu.uiowa.alloy2smt.mapping.MappingSignature;
import edu.uiowa.alloy2smt.mapping.MappingType;
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class Alloy2SmtTranslator extends AbstractTranslator
{
    public final AlloySettings alloySettings;
    final CompModule alloyModel;
    final List<Sig> reachableSigs;
    final List<Sig> topLevelSigs;
    final List<Command> commands;

    final SignatureTranslator signatureTranslator;
    final ExprTranslator exprTranslator;

    Set<String> funcNames;
    Map<Sig, Expr> sigFacts;

    Map<String, String> funcNamesMap;
    Map<String, List<String>> setComprehensionFuncNameToInputsMap;
    Map<String, Expression> setCompFuncNameToDefMap;
    Map<String, VariableDeclaration> setCompFuncNameToBdVarExprMap;
    Map<Sig, FunctionDeclaration> signaturesMap;
    Map<Sig.Field, FunctionDeclaration> fieldsMap;
    Map<String, Func> nameToFuncMap;
    Map<Expr, Integer> sigToIdMap;

    public Alloy2SmtTranslator(CompModule alloyModel, AlloySettings alloySettings)
    {
        TranslatorUtils.reset();
        this.alloySettings = alloySettings;
        this.smtScript = new SmtScript();
        this.alloyModel = alloyModel;
        this.reachableSigs = new ArrayList<>();
        this.topLevelSigs = new ArrayList<>();
        this.commands = alloyModel.getAllCommands();

        this.signatureTranslator = new SignatureTranslator(this);
        this.comparisonOperations = new HashMap<>();
        this.arithmeticOperations = new HashMap<>();
        this.signaturesMap = new HashMap<>();
        this.funcNamesMap = new HashMap<>();
        this.functionsMap = new HashMap<>();
        this.nameToFuncMap = new HashMap<>();
        this.fieldsMap = new HashMap<>();
        this.sigFacts = new HashMap<>();
        this.funcNames = new HashSet<>();
        this.integerConstants = new HashMap<>();
        this.sigToIdMap = new HashMap<>();

        this.signaturesMap.put(Sig.UNIV, univAtom);
        this.signaturesMap.put(Sig.SIGINT, univInt);
        this.smtScript.addSort(atomSort);
        this.smtScript.addSort(uninterpretedInt);
        this.smtScript.addFunction(uninterpretedIntValue);

        this.functionsMap.put(uninterpretedIntValue.getName(), uninterpretedIntValue);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>();
        this.setCompFuncNameToDefMap = new HashMap<>();
        this.setCompFuncNameToBdVarExprMap = new HashMap<>();
        this.exprTranslator = new ExprTranslator(this);
    }

    public Alloy2SmtTranslator(Alloy2SmtTranslator translator)
    {
        this.alloySettings = translator.alloySettings;
        this.smtScript = new SmtScript(translator.smtScript);
        this.alloyModel = translator.alloyModel;
        this.reachableSigs = new ArrayList<>(translator.reachableSigs);
        this.topLevelSigs = new ArrayList<>(translator.topLevelSigs);
        this.sigToIdMap = new HashMap<>(translator.sigToIdMap);

        this.commands = this.alloyModel.getAllCommands();


        this.signatureTranslator = new SignatureTranslator(this);
        this.comparisonOperations = new HashMap<>(translator.comparisonOperations);
        this.integerConstants = new HashMap<>(translator.integerConstants);
        this.arithmeticOperations = new HashMap<>(translator.arithmeticOperations);
        this.signaturesMap = new HashMap<>(translator.signaturesMap);
        this.funcNamesMap = new HashMap<>(translator.funcNamesMap);
        this.functionsMap = new HashMap<>(translator.functionsMap);
        this.fieldsMap = new HashMap<>(translator.fieldsMap);
        this.sigFacts = new HashMap<>(translator.sigFacts);
        this.funcNames = new HashSet<>(translator.funcNames);

        this.setComprehensionFuncNameToInputsMap = new HashMap<>(translator.setComprehensionFuncNameToInputsMap);
        this.setCompFuncNameToDefMap = new HashMap<>(translator.setCompFuncNameToDefMap);
        this.setCompFuncNameToBdVarExprMap = new HashMap<>(translator.setCompFuncNameToBdVarExprMap);
        this.exprTranslator = new ExprTranslator(this);
    }


    FunctionDeclaration getFunctionFromAlloyName(String name)
    {
        FunctionDeclaration function = functionsMap.get(funcNamesMap.get(name));
        if (function == null)
        {
            throw new RuntimeException("Function " + name + " is not found.");
        }
        return function;
    }

    @Override
    public SmtScript translate()
    {
        translateSpecialFunctions();
        this.signatureTranslator.translateSigs();
        this.signatureTranslator.translateSpecialSigFacts();
        //translateFunctionsAndPredicates();
        this.signatureTranslator.translateSigFacts();
        translateFacts();
        translateSpecialAssertions();
        return this.smtScript;
    }

    private void translateSpecialFunctions()
    {
        this.smtScript.addFunction(atomNone);
        this.smtScript.addFunction(univAtom);
        this.smtScript.addFunction(idenAtom);
        this.smtScript.addFunction(idenInt);
        this.smtScript.addFunction(univInt);
    }

    private void translateSpecialAssertions()
    {
        this.smtScript.addAssertion(new Assertion("", "Empty unary relation definition for Atom", BinaryExpression.Op.EQ.make(this.atomNone.getVariable(), UnaryExpression.Op.EMPTYSET.make(setOfUnaryAtomSort))));
        this.smtScript.addAssertion(new Assertion("", "Universe definition for Atom", BinaryExpression.Op.EQ.make(this.univAtom.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUnaryAtomSort))));
        this.smtScript.addAssertion(new Assertion("", "Universe definition for UninterpretedInt", BinaryExpression.Op.EQ.make(univInt.getVariable(), UnaryExpression.Op.UNIVSET.make(setOfUninterpretedIntTuple))));
        addIdenAtom(atomSort, idenAtom);
        addIdenAtom(uninterpretedInt, idenInt);

        // uninterpretedIntValue is injective function
        VariableDeclaration X = new VariableDeclaration("x", uninterpretedInt, false);
        VariableDeclaration Y = new VariableDeclaration("y", uninterpretedInt, false);
        Expression XEqualsY = BinaryExpression.Op.EQ.make(X.getVariable(), Y.getVariable());
        Expression notXEqualsY = UnaryExpression.Op.NOT.make(XEqualsY);

        Expression XValue = new FunctionCallExpression(uninterpretedIntValue, X.getVariable());
        Expression YValue = new FunctionCallExpression(uninterpretedIntValue, Y.getVariable());

        Expression XValueEqualsYValue = BinaryExpression.Op.EQ.make(XValue, YValue);
        Expression notXValueEqualsYValue = UnaryExpression.Op.NOT.make(XValueEqualsYValue);
        Expression implication = BinaryExpression.Op.IMPLIES.make(notXEqualsY, notXValueEqualsYValue);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implication, X, Y);

        smtScript.addAssertion(new Assertion("", uninterpretedIntValueName + " is injective", forAll));

    }

    private void addIdenAtom(Sort sort, FunctionDeclaration identity)
    {
        // Axiom for identity relation
        VariableDeclaration a = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        VariableDeclaration b = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        MultiArityExpression tupleAB = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, a.getVariable(), b.getVariable());

        BinaryExpression member = BinaryExpression.Op.MEMBER.make(tupleAB, identity.getVariable());

        BinaryExpression equals = BinaryExpression.Op.EQ.make(a.getVariable(), b.getVariable());

        BinaryExpression equiv = BinaryExpression.Op.EQ.make(member, equals);

        QuantifiedExpression idenSemantics = QuantifiedExpression.Op.FORALL.make(equiv, a, b);

        this.smtScript.addAssertion(new Assertion("", "Identity relation definition", idenSemantics));
    }

    private void translateFacts()
    {
        for (Pair<String, Expr> pair : this.alloyModel.getAllFacts())
        {
            exprTranslator.translateFormula(pair.a, pair.b);
        }
    }

    /**
     * @return a mapper that maps signatures's names to the corresponding names
     * in the generated smt script
     */
    public Mapper generateMapper()
    {
        Mapper mapper = new Mapper();
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
            if (!sigToIdMap.keySet().contains(sig))
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

        signature.label = sig.label;
        signature.functionName = TranslatorUtils.getOriginalName(signaturesMap.get(sig).getName());

        signature.id = getSigId(sig);

        // find the ids of the parents
        if (sig instanceof Sig.PrimSig && sig != Sig.UNIV)
        {
            signature.parents.add(getSigId(((Sig.PrimSig) sig).parent));
        }
        else if (sig instanceof Sig.SubsetSig)
        {
            signature.isSubset = true;
            for (Sig parent : ((Sig.SubsetSig) sig).parents)
            {
                signature.parents.add(getSigId(parent));
            }
        }

        signature.builtIn = sig.builtin;
        signature.isAbstract = sig.isAbstract != null;
        signature.isOne = sig.isOne != null;
        signature.isLone = sig.isLone != null;
        signature.isSome = sig.isSome != null;
        signature.isPrivate = sig.isPrivate != null;
        signature.isMeta = sig.isMeta != null;

        if (sig instanceof Sig.SubsetSig)
        {
            signature.isExact = ((Sig.SubsetSig) sig).exact;
        }

        signature.isEnum = sig.isEnum != null;

        return signature;
    }

    private MappingField getField(Sig.Field field)
    {
        MappingField mappingField = new MappingField();

        mappingField.label = field.label;
        mappingField.functionName = TranslatorUtils.getOriginalName(fieldsMap.get(field).getName());
        mappingField.id = getSigId(field);
        mappingField.parentId = getSigId(field.sig);
        mappingField.isPrivate = field.isPrivate != null;
        mappingField.isMeta = field.isMeta != null;
        mappingField.types = getFieldTypes(field);

        return mappingField;
    }

    private List<List<MappingType>> getFieldTypes(Sig.Field field)
    {
        List<List<MappingType>> types = new ArrayList<>();
        for (List<Sig.PrimSig> sigs : field.type().fold())
        {
            List<MappingType> type = new ArrayList<>();
            for (Sig sig : sigs)
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
        mappingSignatureId++;
        return mappingSignatureId;
    }

    /**
     * @param expr can be Sig, Field, or Skolem
     * @return the unique id of the expr it exists in the idMap, or generate  a new id
     */
    public int getSigId(Expr expr)
    {
        Integer id = sigToIdMap.get(expr);

        if (id == null)
        {
            id = getUniqueId();
            sigToIdMap.put(expr, id);
        }
        return id;
    }

    /**
     * @param commandIndex the index of the run command
     * @return a list of assertions that represent the translation
     * of the command
     */
    public List<Assertion> translateCommand(int commandIndex)
    {
        Command command = this.commands.get(commandIndex);

        List<Assertion> assertions = getAssertions(command);

        if (alloySettings.includeCommandScope)
        {
            assertions.addAll(translateSignaturesScope(command));
            assertions.addAll(translateIntScope(command));
        }

        return assertions;
    }

    private List<Assertion> translateIntScope(Command command)
    {
        List<Assertion> assertions = new ArrayList<>();
        int minInteger = -(int) Math.pow(2, command.bitwidth - 1);
        int maxInteger = -minInteger - 1;
        ExprVar x = ExprVar.make(command.pos, "x", Sig.SIGINT.type());
        Expr gte = ExprBinary.Op.GTE.make(command.formula.pos, command.formula.closingBracket, x, ExprConstant.makeNUMBER(minInteger));
        Expr lte = ExprBinary.Op.LTE.make(command.formula.pos, command.formula.closingBracket, x, ExprConstant.makeNUMBER(maxInteger));
        Expr and = ExprList.make(command.formula.pos, command.formula.closingBracket, ExprList.Op.AND, Arrays.asList(gte, lte));
        Expr oneOfInt = ExprUnary.Op.ONEOF.make(null, Sig.SIGINT);
        Decl decl = new Decl(null, null, null, Collections.singletonList(x), oneOfInt);
        Expr all = ExprQt.Op.ALL.make(command.formula.pos, command.formula.closingBracket, Collections.singletonList(decl), and);
        Expression expression = exprTranslator.translateExpr(all, new Environment());
        Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(command.pos),
                "Scope " + command.bitwidth + " Int", expression);
        assertions.add(assertion);
        return assertions;
    }

    private List<Assertion> translateSignaturesScope(Command command)
    {
        List<Assertion> assertions = new ArrayList<>();
        Map<Sig, Map<Sig, Integer>> childrenScope = new HashMap<>();
        for (Sig signature : reachableSigs)
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
                    if (commandScope.isExact || alloyModel.getExactSigs().contains(signature))
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
                    if (alloyModel.getExactSigs().contains(signature))
                    {
                        op = BinaryExpression.Op.EQ;
                    }
                    else
                    {
                        op = BinaryExpression.Op.SUBSET;
                    }

                    if (signature.isTopLevel())
                    {
                        if (signature.isAbstract == null)
                        {
                            // no scope specification is given, default value is used
                            scope = command.overall == -1 ? AlloySettings.defaultScope : command.overall;
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

                if (scope >= 1)
                {
                    List<VariableDeclaration> declarations = new ArrayList<>();
                    Sort sort = signature.type().is_int() ? AbstractTranslator.uninterpretedInt : AbstractTranslator.atomSort;
                    VariableDeclaration firstAtom = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
                    declarations.add(firstAtom);
                    Expression firstTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, firstAtom.getVariable());
                    Expression set = UnaryExpression.Op.SINGLETON.make(firstTuple);
                    for (int i = 1; i < scope; i++)
                    {
                        VariableDeclaration declaration = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
                        declarations.add(declaration);
                        Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, declaration.getVariable());
                        Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple);
                        set = BinaryExpression.Op.UNION.make(singleton, set);
                    }

                    Expression constraint = op.make(variable, set);
                    if (declarations.size() > 1)
                    {
                        List<Expression> expressions = declarations
                                .stream().map(d -> d.getVariable())
                                .collect(Collectors.toList());
                        Expression distinct = MultiArityExpression.Op.DISTINCT.make(expressions);
                        constraint = MultiArityExpression.Op.AND.make(constraint, distinct);
                    }
                    Expression exists = QuantifiedExpression.Op.EXISTS.make(constraint, declarations);
                    Assertion scopeAssertion = AlloyUtils.getAssertion(Collections.singletonList(command.pos),
                            signature.toString() + " scope", exists);
                    assertions.add(scopeAssertion);
                }
            }
        }
        return assertions;
    }

    private List<Assertion> getAssertions(Command command)
    {
        assert (command.formula instanceof ExprList);
        ExprList list = (ExprList) command.formula;
        assert (list.op == ExprList.Op.AND);
        List<Assertion> assertions = new ArrayList<>();

        //ToDo: refactor this line which just prints the command as a comment
        Assertion comment = new Assertion("", command.toString(), BoolConstant.True);
        assertions.add(comment);

        for (Expr argument : list.args)
        {
            // translate only the formulas added by the command and ignore facts
            if (!isFactFormula(argument))
            {
                exprTranslator.translateFormula(argument.toString(), argument);
            }
        }
        return assertions;
    }

    //ToDo: refactor this function by storing positions outside
    private boolean isFactFormula(Expr argument)
    {
        List<Pos> positions = alloyModel.getAllFacts().makeConstList()
                                        .stream().map(p -> p.b.pos).collect(Collectors.toList());
        for (Pos pos : positions)
        {
            if (pos.contains(argument.pos))
            {
                return true;
            }
        }
        return false;
    }

    private int getScope(Sig.PrimSig parent, Command command,
                         Map<Sig, Map<Sig, Integer>> childrenScope)
    {
        int scopeSum = 0;
        Map<Sig, Integer> parentMap = childrenScope.get(parent);
        for (Sig signature : parent.children())
        {
            if (signature.isAbstract == null)
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
                    if (signature.isOne != null)
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

        if (scopeSum == 0) // no explicit scope for children is given
        {
            scopeSum = command.overall == -1 ? AlloySettings.defaultScope : command.overall;
        }
        return scopeSum;
    }
}
