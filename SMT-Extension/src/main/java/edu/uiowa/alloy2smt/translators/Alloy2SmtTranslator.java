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
import edu.uiowa.smt.SmtEnv;
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

  Map<Sig, Expr> sigFacts;
  Map<Sig, FunctionDeclaration> signaturesMap;
  Map<Sig.Field, FunctionDeclaration> fieldsMap;
  Map<Expr, Integer> sigToIdMap;
  List<Expr> facts;

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
    this.functionsMap = new HashMap<>();
    this.fieldsMap = new HashMap<>();
    this.sigFacts = new HashMap<>();
    this.sigToIdMap = new HashMap<>();

    this.signaturesMap.put(Sig.UNIV, univAtom);
    this.signaturesMap.put(Sig.SIGINT, univInt);
    this.smtScript.addSort(atomSort);
    this.smtScript.addSort(uninterpretedInt);
    this.smtScript.addFunction(uninterpretedIntValue);

    this.functionsMap.put(uninterpretedIntValue.getName(), uninterpretedIntValue);

    this.exprTranslator = new ExprTranslator(this);
    this.facts = new ArrayList<>();
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
    this.arithmeticOperations = new HashMap<>(translator.arithmeticOperations);
    this.signaturesMap = new HashMap<>(translator.signaturesMap);
    this.functionsMap = new HashMap<>(translator.functionsMap);
    this.fieldsMap = new HashMap<>(translator.fieldsMap);
    this.sigFacts = new HashMap<>(translator.sigFacts);

    this.exprTranslator = new ExprTranslator(this);
    this.facts = new ArrayList<>(translator.facts);
  }

  @Override
  public SmtScript translate()
  {
    translateSpecialFunctions();
    this.signatureTranslator.translateSigs();
    this.signatureTranslator.translateSpecialSigFacts();
    this.signatureTranslator.translateSigFacts();
    translateFacts();
    translateSpecialAssertions();
    translateFunctions();
    return this.smtScript;
  }

  private void translateFunctions()
  {
    for (CompModule module : alloyModel.getAllReachableModules())
    {
      if (module.getModelName().contains("util/ordering") ||
          module.getModelName().contains("util/integer"))
      {
        continue;
      }
      for (Func func : module.getAllFunc())
      {
        getFuncTranslation(func);
      }
    }
  }

  private void translateSpecialFunctions()
  {
    this.smtScript.addFunction(atomNone);
    this.smtScript.addFunction(univAtom);
    this.smtScript.addFunction(idenAtom);
    this.smtScript.addFunction(idenInt);
    this.smtScript.addFunction(univInt);
  }

  private void translateFacts()
  {
    for (CompModule module : alloyModel.getAllReachableModules())
    {
      for (Pair<String, Expr> pair : module.getAllFacts())
      {
        exprTranslator.translateFormula(pair.a, pair.b);
        this.facts.add(pair.b);
      }
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
  public void translateCommand(int commandIndex)
  {
    // set the current smt script to a new child for push pop commands
    this.smtScript = smtScript.createChild();

    Command command = this.commands.get(commandIndex);

    translatecommandExprList(command);

    if (alloySettings.includeCommandScope)
    {
      translateSignaturesScope(command);
      translateIntScope(command);
    }

    // restore the parent for new alloy commands
    this.smtScript = this.smtScript.getParent();
  }

  private void translateIntScope(Command command)
  {
    int minInteger = -(int) Math.pow(2, command.bitwidth - 1);
    int maxInteger = -minInteger - 1;
    ExprVar x = ExprVar.make(command.pos, "x", Sig.SIGINT.type());
    Expr gte = ExprBinary.Op.GTE.make(command.formula.pos, command.formula.closingBracket, x, ExprConstant.makeNUMBER(minInteger));
    Expr lte = ExprBinary.Op.LTE.make(command.formula.pos, command.formula.closingBracket, x, ExprConstant.makeNUMBER(maxInteger));
    Expr and = ExprList.make(command.formula.pos, command.formula.closingBracket, ExprList.Op.AND, Arrays.asList(gte, lte));
    Expr oneOfInt = ExprUnary.Op.ONEOF.make(null, Sig.SIGINT);
    Decl decl = new Decl(null, null, null, null, Collections.singletonList(x), oneOfInt);
    Expr all = ExprQt.Op.ALL.make(command.formula.pos, command.formula.closingBracket, Collections.singletonList(decl), and);
    exprTranslator.translateFormula("Scope " + command.bitwidth + " Int", all);
  }

  private void translateSignaturesScope(Command command)
  {
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
        SmtBinaryExpr.Op op;
        if (optional.isPresent())
        {
          CommandScope commandScope = optional.get();
          if (commandScope.isExact || alloyModel.getExactSigs().contains(signature))
          {
            op = SmtBinaryExpr.Op.EQ;
          }
          else
          {
            op = SmtBinaryExpr.Op.SUBSET;
          }
          scope = commandScope.endingScope;
        }
        else
        {
          if (alloyModel.getExactSigs().contains(signature))
          {
            op = SmtBinaryExpr.Op.EQ;
          }
          else
          {
            op = SmtBinaryExpr.Op.SUBSET;
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

        SmtExpr variable = signaturesMap.get(signature).getVariable();

        if (scope >= 1)
        {
          List<SmtVariable> declarations = new ArrayList<>();
          Sort sort = signature.type().is_int() ? AbstractTranslator.uninterpretedInt : AbstractTranslator.atomSort;
          SmtVariable firstAtom = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
          declarations.add(firstAtom);
          SmtExpr firstTuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, firstAtom.getVariable());
          SmtExpr set = SmtUnaryExpr.Op.SINGLETON.make(firstTuple);
          for (int i = 1; i < scope; i++)
          {
            SmtVariable declaration = new SmtVariable(TranslatorUtils.getFreshName(sort), sort, false);
            declarations.add(declaration);
            SmtExpr tuple = new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, declaration.getVariable());
            SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(tuple);
            set = SmtBinaryExpr.Op.UNION.make(singleton, set);
          }

          SmtExpr constraint = op.make(variable, set);
          if (declarations.size() > 1)
          {
            List<SmtExpr> smtExprs = declarations
                .stream().map(d -> d.getVariable())
                .collect(Collectors.toList());
            SmtExpr distinct = SmtMultiArityExpr.Op.DISTINCT.make(smtExprs);
            constraint = SmtMultiArityExpr.Op.AND.make(constraint, distinct);
          }
          SmtExpr exists = SmtQtExpr.Op.EXISTS.make(constraint, declarations);
          Assertion scopeAssertion = AlloyUtils.getAssertion(Collections.singletonList(command.pos),
              signature.toString() + " scope", exists);
          smtScript.addAssertion(scopeAssertion);
        }
      }
    }
  }

  private void translatecommandExprList(Command command)
  {
    assert (command.formula instanceof ExprList);
    ExprList list = (ExprList) command.formula;
    assert (list.op == ExprList.Op.AND);

    //ToDo: refactor this line which just prints the command as a comment
    Assertion comment = new Assertion("", command.toString(), BoolConstant.True);
    smtScript.addAssertion(comment);

    for (Expr argument : list.args)
    {
      // translate only the formulas added by the command and ignore facts
      if (!facts.contains(argument))
      {
        exprTranslator.translateFormula(argument.toString(), argument);
      }
    }
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

  public FunctionDeclaration getFuncTranslation(Func func)
  {
    FunctionDeclaration function;
    if(functionsMap.containsKey(func.label))
    {
      function = functionsMap.get(func.label);
    }
    else
    {
      function = translateFunc(func);
    }
    return function;
  }

  private FunctionDefinition translateFunc(Func func)
  {
    SmtEnv smtEnv = new SmtEnv();
    List<SmtVariable> arguments = new ArrayList<>();
    for (Decl decl : func.decls)
    {
      List<SmtVariable> variables = exprTranslator.declTranslator.translateDecl(decl, smtEnv);
      List<SmtVariable> setVariables = convertToSetVariables(variables);
      arguments.addAll(setVariables);
    }
    // add arguments to function environment
    for (SmtVariable variable : arguments)
    {
      smtEnv.put(variable.getName(), variable.getVariable());
    }

    SmtExpr smtExpr = exprTranslator.translateExpr(func.getBody(), smtEnv);

    FunctionDefinition function = new FunctionDefinition(func.label, arguments, smtExpr.getSort(), smtExpr, true);

    addFunction(function);

    return function;
  }

  private List<SmtVariable> convertToSetVariables(List<SmtVariable> variables)
  {
    List<SmtVariable> setVariables = new ArrayList<>();

    for (SmtVariable variable : variables)
    {
      if (variable.getSort() instanceof TupleSort)
      {
        Sort sort = new SetSort(variable.getSort());
        SmtVariable newVariable = new SmtVariable(variable.getName(), sort, variable.isOriginal());
        setVariables.add(newVariable);
      }
      else
      {
        setVariables.add(variable);
      }
    }
    return setVariables;
  }
}
