package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;
import java.util.stream.Collectors;

public class ExprQtTranslator
{
  final ExprTranslator exprTranslator;
  final ExprUnaryTranslator exprUnaryTranslator;
  final ExprBinaryTranslator exprBinaryTranslator;
  final Alloy2SmtTranslator translator;

  public ExprQtTranslator(ExprTranslator exprTranslator)
  {
    this.exprTranslator = exprTranslator;
    this.exprUnaryTranslator = exprTranslator.exprUnaryTranslator;
    this.exprBinaryTranslator = exprTranslator.exprBinaryTranslator;
    this.translator = exprTranslator.translator;
  }

  SmtExpr translateExprQt(ExprQt exprQt, Environment environment)
  {
    // create a new scope for quantified variables
    Environment newEnvironment = new Environment(environment);
    Map<String, SmtExpr> ranges = new LinkedHashMap<>();

    // this variable maintains the multiplicity constraints for declared variables
    // x: [one, lone, some, set] e
    SmtExpr multiplicityConstraints = BoolConstant.True;
    multiplicityConstraints = declareQuantifiedVariables(exprQt, newEnvironment, ranges, multiplicityConstraints);

    SmtExpr quantifiersConstraints = multiplicityConstraints;

    SmtExpr disjointConstraints = getDisjointConstraints(exprQt, newEnvironment);

    if (!disjointConstraints.equals(BoolConstant.True))
    {
      quantifiersConstraints = SmtMultiArityExpr.Op.AND.make(quantifiersConstraints, disjointConstraints);
    }

    // translate the body of the quantified expression
    SmtExpr body = exprTranslator.translateExpr(exprQt.sub, newEnvironment);
    switch (exprQt.op)
    {
      case ALL:
        return translateAllQuantifier(body, ranges, newEnvironment, quantifiersConstraints);
      case NO:
        return translateNoQuantifier(body, ranges, newEnvironment, quantifiersConstraints);
      case SOME:
        return translateSomeQuantifier(body, ranges, newEnvironment, quantifiersConstraints);
      case ONE:
        return translateOneQuantifier(body, ranges, newEnvironment, quantifiersConstraints);
      case LONE:
        return translateLoneQuantifier(body, ranges, newEnvironment, quantifiersConstraints);
      case COMPREHENSION:
        return translateComprehension(exprQt, body, ranges, newEnvironment);
      default:
        throw new UnsupportedOperationException();
    }
//        throw new UnsupportedOperationException();
  }

  private SmtExpr declareQuantifiedVariables(ExprQt exprQt, Environment newEnvironment, Map<String, SmtExpr> ranges, SmtExpr multiplicityConstraints)
  {
    for (Decl decl : exprQt.decls)
    {
      SmtExpr range = exprTranslator.translateExpr(decl.expr, newEnvironment);
      for (ExprHasName name : decl.names)
      {
        ranges.put(name.label, range);
        String label = name.label;
        SetSort setSort = (SetSort) range.getSort();
        SmtVariable variable = getVariableDeclaration(decl.expr, label, setSort, range);
        SmtExpr constraint = getMultiplicityConstraint(decl.expr, variable, setSort);
        multiplicityConstraints = SmtMultiArityExpr.Op.AND.make(multiplicityConstraints, constraint);
        newEnvironment.put(name.label, variable.getVariable());
      }
    }
    return multiplicityConstraints;
  }


  private SmtExpr getDisjointConstraints(ExprQt exprQt, Environment newEnvironment)
  {
    SmtExpr disjointConstraints = BoolConstant.True;

    for (Decl decl : exprQt.decls)
    {
      // disjoint fields
      if (decl.disjoint != null && decl.names.size() > 1)
      {
        for (int i = 0; i < decl.names.size() - 1; i++)
        {
          for (int j = i + 1; j < decl.names.size(); j++)
          {
            SmtExpr variableI = newEnvironment.get(decl.names.get(i).label);
            SmtExpr variableJ = newEnvironment.get(decl.names.get(j).label);

            if (variableJ.getSort() instanceof UninterpretedSort)
            {
              throw new UnsupportedOperationException();
            }

            if (variableJ.getSort() instanceof TupleSort)
            {
              variableI = SmtUnaryExpr.Op.SINGLETON.make(variableI);
              variableJ = SmtUnaryExpr.Op.SINGLETON.make(variableJ);
            }

            SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(variableI, variableJ);
            SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(variableI.getSort());
            SmtExpr equal = SmtBinaryExpr.Op.EQ.make(intersect, emptySet);
            disjointConstraints = SmtMultiArityExpr.Op.AND.make(disjointConstraints, equal);
          }
        }
      }
    }
    return disjointConstraints;
  }

  private SmtExpr translateComprehension(ExprQt exprQt, SmtExpr body, Map<String, SmtExpr> ranges, Environment environment)
  {
    // {x: e1, y: e2, ... | f} is translated into
    // declare-fun comprehension(freeVariables): (e1 x e2 x ...)
    // assert forall x, y,... (x in e1 and y in e2 ... and f <=>
    // (x, y, ...) in comprehension(freeVariables))

    List<SmtVariable> quantifiedVariables = ranges.entrySet()
                                                  .stream()
                                                  .map(entry -> (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                  .collect(Collectors.toList());

    List<Sort> elementSorts = quantifiedVariables.stream()
                                                 .map(v -> ((TupleSort) (v.getSort())).elementSorts.get(0))
                                                 .collect(Collectors.toList());

    Sort returnSort = new SetSort(new TupleSort(elementSorts));

    SmtExpr membership = getMemberOrSubsetExpressions(ranges, environment);

    // add variables in the environment as arguments to the set function
    LinkedHashMap<String, SmtExpr> argumentsMap = environment.getParent().getVariables();
    List<Sort> argumentSorts = new ArrayList<>();
    List<SmtExpr> arguments = new ArrayList<>();
    List<SmtVariable> quantifiedArguments = new ArrayList<>();
    for (Map.Entry<String, SmtExpr> argument : argumentsMap.entrySet())
    {
      Variable variable = (Variable) argument.getValue();
      arguments.add(variable);
      Sort sort = variable.getSort();
      argumentSorts.add(sort);

      // handle set sorts differently to avoid second order quantification
      if (sort instanceof SetSort)
      {
        Sort elementSort = ((SetSort) sort).elementSort;
        SmtVariable tuple = new SmtVariable(variable.getName(), elementSort, variable.isOriginal());
        quantifiedArguments.add(tuple);
        SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(tuple.getVariable());
        body = body.replace(variable, singleton);
        membership = membership.replace(argument.getValue(), singleton);
      }
      else if (sort instanceof TupleSort || sort instanceof UninterpretedSort)
      {
        quantifiedArguments.add((SmtVariable) variable.getDeclaration());
      }
      else
      {
        throw new UnsupportedOperationException();
      }
    }
    FunctionDeclaration setFunction = new FunctionDeclaration(TranslatorUtils.getFreshName(returnSort), argumentSorts, returnSort, false);
    translator.smtScript.addFunction(setFunction);

    SmtExpr setFunctionSmtExpr;
    if (argumentSorts.size() == 0)
    {
      setFunctionSmtExpr = setFunction.getVariable();
    }
    else
    {
      List<SmtExpr> smtExprs = AlloyUtils.getFunctionCallArguments(quantifiedArguments, argumentsMap);
      setFunctionSmtExpr = new SmtCallExpr(setFunction, smtExprs);
    }

    List<SmtExpr> quantifiedSmtExprs = quantifiedVariables.stream()
                                                          .map(v -> SmtBinaryExpr.Op.TUPSEL.make(IntConstant.getInstance(0), v.getVariable()))
                                                          .collect(Collectors.toList());

    SmtExpr tuple = SmtMultiArityExpr.Op.MKTUPLE.make(quantifiedSmtExprs);

    SmtExpr tupleMember = SmtBinaryExpr.Op.MEMBER.make(tuple, setFunctionSmtExpr);

    SmtExpr and = SmtMultiArityExpr.Op.AND.make(membership, body);

    SmtExpr equivalence = SmtBinaryExpr.Op.EQ.make(tupleMember, and);

    // add variables defined in functions, predicates or let expression to the list of quantifiers
    quantifiedArguments.addAll(quantifiedVariables);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(equivalence, quantifiedArguments);

    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(exprQt.pos),
        exprQt.toString(), forAll);
    translator.smtScript.addAssertion(assertion);

    if (argumentSorts.size() == 0)
    {
      return setFunction.getVariable();
    }
    else
    {
      return new SmtCallExpr(setFunction, arguments);
    }
  }


  private SmtVariable getVariableDeclaration(Expr expr, String variableName, SetSort setSort, SmtExpr range)
  {
    if (expr instanceof Sig)
    {
      return getVariableDeclaration(variableName, setSort, range);
    }
    if (expr instanceof ExprUnary)
    {
      ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
      switch (multiplicityOperator)
      {

        case ONEOF:
        {
          return getVariableDeclaration(variableName, setSort, range);
        }
        case SOMEOF: // same as SETOF
        case LONEOF: // same as SETOF
        case NOOP: // only happens with relations
        case SETOF:
        {
          SmtVariable declaration = new SmtVariable(variableName, setSort, true);
          SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(declaration.getVariable(), range);
          declaration.setConstraint(subset);
          return declaration;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    if (expr instanceof ExprBinary)
    {
      ExprBinary.Op multiplicityOperator = ((ExprBinary) expr).op;
      switch (multiplicityOperator)
      {
        case ARROW:
        case ANY_ARROW_SOME:
        case ANY_ARROW_ONE:
        case ANY_ARROW_LONE:
        case SOME_ARROW_ANY:
        case SOME_ARROW_SOME:
        case SOME_ARROW_ONE:
        case SOME_ARROW_LONE:
        case ONE_ARROW_ANY:
        case ONE_ARROW_SOME:
        case ONE_ARROW_ONE:
        case ONE_ARROW_LONE:
        case LONE_ARROW_ANY:
        case LONE_ARROW_SOME:
        case LONE_ARROW_ONE:
        case LONE_ARROW_LONE:
        {
          SmtVariable declaration = new SmtVariable(variableName, setSort, true);
          SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(declaration.getVariable(), range);
          declaration.setConstraint(subset);
          return declaration;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    throw new UnsupportedOperationException();
  }

  private SmtVariable getVariableDeclaration(String variableName, SetSort setSort, SmtExpr range)
  {
    SmtVariable declaration = new SmtVariable(variableName, setSort.elementSort, true);
    SmtExpr member = SmtBinaryExpr.Op.MEMBER.make(declaration.getVariable(), range);
    declaration.setConstraint(member);
    return declaration;
  }

  private SmtExpr getMultiplicityConstraint(Expr expr, SmtVariable variable, SetSort setSort)
  {
    if (expr instanceof ExprUnary)
    {
      ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
      SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(setSort);
      switch (multiplicityOperator)
      {
        case NOOP: // same as ONEOF
        case ONEOF:
        {
          // variable.getSort() is a tuple sort, so there is no constraint
          return BoolConstant.True;
        }
        case SOMEOF:
        {
          // the set is not empty
          SmtExpr empty = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), emptySet);
          SmtExpr notEmpty = SmtUnaryExpr.Op.NOT.make(empty);
          return notEmpty;
        }
        case SETOF:
        {
          // variable.getSort() is a set, so there is no constraint
          return BoolConstant.True;
        }
        case LONEOF:
        {
          // either the set is empty or a singleton
          SmtExpr empty = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), emptySet);
          SmtVariable singleElement = new SmtVariable(TranslatorUtils.getFreshName(setSort.elementSort), setSort.elementSort, false);
          SmtExpr singleton = SmtUnaryExpr.Op.SINGLETON.make(singleElement.getVariable());
          SmtExpr isSingleton = SmtBinaryExpr.Op.EQ.make(variable.getVariable(), singleton);
          SmtExpr emptyOrSingleton = SmtMultiArityExpr.Op.OR.make(empty, isSingleton);
          SmtExpr exists = SmtQtExpr.Op.EXISTS.make(emptyOrSingleton, singleElement);
          return exists;
        }
        default:
          throw new UnsupportedOperationException();
      }
    }
    if (expr instanceof ExprBinary)
    {
      return BoolConstant.True;
    }
    throw new UnsupportedOperationException();
  }

  private SmtExpr translateAllQuantifier(SmtExpr body, Map<String, SmtExpr> ranges,
                                         Environment environment, SmtExpr multiplicityConstraints)
  {
    // all x: e1, y: e2, ... | f is translated into
    // forall x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints implies f)


    List<SmtVariable> quantifiedVariables = ranges.entrySet()
                                                  .stream()
                                                  .map(entry -> (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                  .collect(Collectors.toList());

    SmtExpr memberOrSubset = getMemberOrSubsetExpressions(ranges, environment);
    SmtExpr and = SmtMultiArityExpr.Op.AND.make(memberOrSubset, multiplicityConstraints);
    SmtQtExpr exists = environment.getAuxiliaryFormula();

    if (exists != null)
    {
      SmtExpr and2 = SmtMultiArityExpr.Op.AND.make(exists.getExpression(), and);
      exists = SmtQtExpr.Op.EXISTS.make(and2, exists.getVariables());
      environment.clearAuxiliaryFormula();
    }

    body = SmtBinaryExpr.Op.IMPLIES.make(exists, body);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(body, quantifiedVariables);

    SmtExpr translation = exprTranslator.translateAuxiliaryFormula(forAll, environment);
    return translation;
  }

  private SmtExpr translateNoQuantifier(SmtExpr body, Map<String, SmtExpr> ranges,
                                        Environment environment, SmtExpr multiplicityConstraints)
  {
    SmtExpr notBody = SmtUnaryExpr.Op.NOT.make(body);
    return translateAllQuantifier(notBody, ranges, environment, multiplicityConstraints);
  }

  private SmtExpr translateSomeQuantifier(SmtExpr body, Map<String, SmtExpr> ranges,
                                          Environment environment, SmtExpr multiplicityConstraints)
  {

    // some x: e1, y: e2, ... | f is translated into
    // exists x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints and f)

    List<SmtVariable> quantifiedVariables = ranges.entrySet()
                                                  .stream()
                                                  .map(entry -> (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                  .collect(Collectors.toList());

    SmtMultiArityExpr and = SmtMultiArityExpr.Op.AND.make(
        getMemberOrSubsetExpressions(ranges, environment),
        multiplicityConstraints, body);

    SmtQtExpr existsSet = environment.getAuxiliaryFormula();
    if (existsSet != null)
    {
      List<SmtExpr> smtExprs = new ArrayList<>(and.getExpressions());
      smtExprs.add(existsSet.getExpression());
      and = SmtMultiArityExpr.Op.AND.make(smtExprs);
      SmtExpr exists = SmtQtExpr.Op.EXISTS.make(and, existsSet.getVariables());
      return SmtQtExpr.Op.EXISTS.make(exists, quantifiedVariables);
    }
    else
    {
      SmtExpr exists = SmtQtExpr.Op.EXISTS.make(and, quantifiedVariables);
      return exists;
    }
  }

  private SmtExpr getMemberOrSubsetExpressions(Map<String, SmtExpr> ranges, Environment environment)
  {
    SmtExpr and = BoolConstant.True;
    for (Map.Entry<String, SmtExpr> entry : ranges.entrySet())
    {
      SmtVariable variable = (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration();
      SmtExpr memberOrSubset;
      if (variable.getSort() instanceof TupleSort)
      {
        memberOrSubset = SmtBinaryExpr.Op.MEMBER.make(variable.getVariable(), entry.getValue());
      }
      else if (variable.getSort() instanceof SetSort)
      {
        memberOrSubset = SmtBinaryExpr.Op.SUBSET.make(variable.getVariable(), entry.getValue());
      }
      else
      {
        throw new UnsupportedOperationException(variable.getSort().toString());
      }
      and = SmtMultiArityExpr.Op.AND.make(and, memberOrSubset);
    }
    return and;
  }

  private SmtExpr translateOneQuantifier(SmtExpr body, Map<String, SmtExpr> ranges,
                                         Environment environment, SmtExpr multiplicityConstraints)
  {
    // one x: e1, y: e2, ... | f(x, y, ...) is translated into
    // exists x, y, ... ( x in e1 and y in e2 and ... and multiplicityConstraints(x, y, ...) and f(x, y, ...) and
    //                      for all x', y', ... (x in e1 and y in e2 ... and multiplicityConstraints(x', y', ...)
    //                              and not (x' = x and y' = y ...) implies not f(x', y', ...)))

    List<SmtVariable> oldVariables = ranges.entrySet()
                                           .stream()
                                           .map(entry -> (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                           .collect(Collectors.toList());

    SmtExpr oldMemberOrSubset = getMemberOrSubsetExpressions(ranges, environment);

    SmtExpr existsAnd = SmtMultiArityExpr.Op.AND.make(oldMemberOrSubset, multiplicityConstraints);

    existsAnd = SmtMultiArityExpr.Op.AND.make(existsAnd, body);

    List<SmtVariable> newVariables = new ArrayList<>();

    SmtExpr newBody = body;
    SmtExpr oldEqualNew = BoolConstant.True;
    SmtExpr newMemberOrSubset = BoolConstant.True;
    SmtExpr newMultiplicityConstraints = multiplicityConstraints;
    for (Map.Entry<String, SmtExpr> entry : ranges.entrySet())
    {
      SmtVariable oldVariable = (SmtVariable) ((Variable) environment.get(entry.getKey())).getDeclaration();
      SmtVariable newVariable = new SmtVariable(TranslatorUtils.getFreshName(oldVariable.getSort()), oldVariable.getSort(), false);
      if (oldVariable.getConstraint() != null)
      {
        SmtExpr newConstraint = oldVariable.getConstraint().substitute(oldVariable.getVariable(), newVariable.getVariable());
        newVariable.setConstraint(newConstraint);
      }

      newVariables.add(newVariable);
      newBody = newBody.substitute(oldVariable.getVariable(), newVariable.getVariable());
      newMultiplicityConstraints = newMultiplicityConstraints.substitute(oldVariable.getVariable(), newVariable.getVariable());

      oldEqualNew = SmtMultiArityExpr.Op.AND.make(oldEqualNew, SmtBinaryExpr.Op.EQ.make(oldVariable.getVariable(), newVariable.getVariable()));
      if (newVariable.getSort() instanceof TupleSort)
      {
        newMemberOrSubset = SmtMultiArityExpr.Op.AND.make(newMemberOrSubset, SmtBinaryExpr.Op.MEMBER.make(newVariable.getVariable(), entry.getValue()));
      }
      else if (newVariable.getSort() instanceof SetSort)
      {
        newMemberOrSubset = SmtMultiArityExpr.Op.AND.make(newMemberOrSubset, SmtBinaryExpr.Op.SUBSET.make(newVariable.getVariable(), entry.getValue()));
      }
      else
      {
        throw new UnsupportedOperationException();
      }
    }


    newBody = SmtUnaryExpr.Op.NOT.make(newBody);
    SmtExpr notOldEqualNew = SmtUnaryExpr.Op.NOT.make(oldEqualNew);

    SmtExpr forAllAnd = SmtMultiArityExpr.Op.AND.make(newMemberOrSubset, newMultiplicityConstraints);
    forAllAnd = SmtMultiArityExpr.Op.AND.make(forAllAnd, notOldEqualNew);

    SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(forAllAnd, newBody);
    SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, newVariables);
    existsAnd = SmtMultiArityExpr.Op.AND.make(existsAnd, forAll);
    SmtExpr exists = SmtQtExpr.Op.EXISTS.make(existsAnd, oldVariables);
    return exists;
  }

  private SmtExpr translateLoneQuantifier(SmtExpr body, Map<String, SmtExpr> ranges,
                                          Environment environment, SmtExpr multiplicityConstraints)
  {
    // lone ... | f is translated into
    // (all ... | not f)  or (one ... | f)

    SmtExpr notBody = SmtUnaryExpr.Op.NOT.make(body);
    SmtExpr allNot = translateAllQuantifier(notBody, ranges, environment, multiplicityConstraints);
    SmtExpr one = translateOneQuantifier(body, ranges, environment, multiplicityConstraints);
    SmtExpr or = SmtMultiArityExpr.Op.OR.make(allNot, one);
    return or;
  }
}
