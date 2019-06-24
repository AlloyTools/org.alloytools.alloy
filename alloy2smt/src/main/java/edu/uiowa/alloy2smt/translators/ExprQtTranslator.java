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

    Expression translateExprQt(ExprQt exprQt, Environment environment)
    {
        // create a new scope for quantified variables
        Environment newEnvironment = new Environment(environment);
        Map<String, Expression> ranges = new LinkedHashMap<>();

        // this variable maintains the multiplicity constraints for declared variables
        // x: [one, lone, some, set] e
        Expression multiplicityConstraints = BoolConstant.True;
        multiplicityConstraints = declareQuantifiedVariables(exprQt, newEnvironment, ranges, multiplicityConstraints);

        Expression quantifiersConstraints = multiplicityConstraints;

        Expression disjointConstraints =  getDisjointConstraints(exprQt,  newEnvironment);

        if(!disjointConstraints.equals(BoolConstant.True))
        {
            quantifiersConstraints = BinaryExpression.Op.AND.make(quantifiersConstraints, disjointConstraints);
        }
        
        // translate the body of the quantified expression
        Expression body = exprTranslator.translateExpr(exprQt.sub, newEnvironment);

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

    private Expression declareQuantifiedVariables(ExprQt exprQt, Environment newEnvironment, Map<String, Expression> ranges, Expression multiplicityConstraints)
    {
        for (Decl decl : exprQt.decls)
        {
            Expression range = exprTranslator.translateExpr(decl.expr, newEnvironment);
            for (ExprHasName name : decl.names)
            {
                ranges.put(name.label, range);
                String label = name.label;
                SetSort setSort = (SetSort) range.getSort();
                VariableDeclaration variable;
                variable = getVariableDeclaration(decl.expr, label, setSort, range);
                Expression constraint = getMultiplicityConstraint(decl.expr, variable, setSort);
                multiplicityConstraints = BinaryExpression.Op.AND.make(multiplicityConstraints, constraint);
                newEnvironment.put(name.label, variable.getVariable());
            }
        }
        return multiplicityConstraints;
    }


    private Expression getDisjointConstraints(ExprQt exprQt, Environment newEnvironment)
    {
        Expression disjointConstraints = BoolConstant.True;

        for (Decl decl : exprQt.decls)
        {
            // disjoint fields
            if (decl.disjoint != null && decl.names.size() > 1)
            {
                for (int i = 0; i < decl.names.size() - 1; i++)
                {
                    for (int j = i + 1; j < decl.names.size(); j++)
                    {
                        Expression variableI = newEnvironment.get(decl.names.get(i).label);
                        Expression variableJ = newEnvironment.get(decl.names.get(j).label);

                        if(variableJ.getSort() instanceof UninterpretedSort)
                        {
                            throw new UnsupportedOperationException();
                        }

                        if(variableJ.getSort() instanceof TupleSort)
                        {
                            variableI = UnaryExpression.Op.SINGLETON.make(variableI);
                            variableJ = UnaryExpression.Op.SINGLETON.make(variableJ);
                        }

                        Expression intersect = BinaryExpression.Op.INTERSECTION.make(variableI, variableJ);
                        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(variableI.getSort());
                        Expression equal = BinaryExpression.Op.EQ.make(intersect, emptySet);
                        disjointConstraints = BinaryExpression.Op.AND.make(disjointConstraints, equal);
                    }
                }
            }
        }
        return disjointConstraints;
    }

    private Expression translateComprehension(ExprQt exprQt, Expression body, Map<String, Expression> ranges, Environment environment)
    {
        // {x: e1, y: e2, ... | f} is translated into
        // declare-fun comprehension(freeVariables): (e1 x e2 x ...)
        // assert forall x, y,... (x in e1 and y in e2 ... and f <=>
        // (x, y, ...) in comprehension(freeVariables))

        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                             .collect(Collectors.toList());

        List<Sort> elementSorts = quantifiedVariables.stream()
                .map(v -> ((TupleSort) (v.getSort())).elementSorts.get(0))
                .collect(Collectors.toList());

        Sort returnSort = new SetSort(new TupleSort(elementSorts));

        Expression membership = getMemberOrSubsetExpressions(ranges, environment);

        // add variables in the environment as arguments to the set function
        LinkedHashMap<String, Expression> argumentsMap = environment.getParent().getVariables();
        List<Sort> argumentSorts = new ArrayList<>();
        List<Expression> arguments = new ArrayList<>();
        List<VariableDeclaration> quantifiedArguments = new ArrayList<>();
        for (Map.Entry<String, Expression> argument: argumentsMap.entrySet())
        {
            Variable variable = (Variable) argument.getValue();
            arguments.add(variable);
            Sort sort = variable.getSort();
            argumentSorts.add(sort);

            // handle set sorts differently to avoid second order quantification
            if(sort instanceof SetSort)
            {
                Sort elementSort = ((SetSort) sort).elementSort;
                VariableDeclaration tuple = new VariableDeclaration(variable.getName(), elementSort, null);
                quantifiedArguments.add(tuple);
                Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple.getVariable());
                body = body.replace(variable, singleton);
                membership = membership.replace(argument.getValue(), singleton);
            }
            else if (sort instanceof TupleSort || sort instanceof UninterpretedSort)
            {
                quantifiedArguments.add((VariableDeclaration) variable.getDeclaration());
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }
        FunctionDeclaration setFunction = new FunctionDeclaration(TranslatorUtils.getNewSetName(), argumentSorts, returnSort);
        translator.smtProgram.addFunction(setFunction);

        Expression setFunctionExpression;
        if(argumentSorts.size() == 0)
        {
            setFunctionExpression = setFunction.getVariable();
        }
        else
        {
            List<Expression> expressions = AlloyUtils.getFunctionCallArguments(quantifiedArguments, argumentsMap);
            setFunctionExpression = new FunctionCallExpression(setFunction, expressions);
        }

        List<Expression> quantifiedExpressions = quantifiedVariables.stream()
                    .map(v -> BinaryExpression.Op.TUPSEL.make(IntConstant.getInstance(0), v.getVariable()))
                    .collect(Collectors.toList());

        Expression tuple = MultiArityExpression.Op.MKTUPLE.make(quantifiedExpressions);

        Expression tupleMember = BinaryExpression.Op.MEMBER.make(tuple, setFunctionExpression);

        Expression and = BinaryExpression.Op.AND.make(membership, body);

        Expression equivalence = BinaryExpression.Op.EQ.make(tupleMember, and);

        // add variables defined in functions, predicates or let expression to the list of quantifiers
        quantifiedArguments.addAll(quantifiedVariables);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(equivalence, quantifiedArguments);

        Assertion assertion = new Assertion(exprQt.toString(), forAll);
        translator.smtProgram.addAssertion(assertion);

        if(argumentSorts.size() == 0)
        {
            return setFunction.getVariable();
        }
        else
        {
            return new FunctionCallExpression(setFunction, arguments);
        }
    }


    private VariableDeclaration getVariableDeclaration(Expr expr, String variableName, SetSort setSort, Expression range)
    {
        if(expr instanceof Sig)
        {
            return getVariableDeclaration(variableName, setSort, range);
        }
        if(expr instanceof ExprUnary)
        {
            ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
            switch (multiplicityOperator)
            {
                case NOOP: // same as ONEOF
                case ONEOF:
                {
                    return getVariableDeclaration(variableName, setSort, range);
                }
                case SOMEOF: // same as SETOF
                case LONEOF: // same as SETOF
                case SETOF:
                {
                    VariableDeclaration declaration = new VariableDeclaration(variableName, setSort, null);
                    Expression subset = BinaryExpression.Op.SUBSET.make(declaration.getVariable(), range);
                    declaration.setConstraint(subset);
                    return declaration;
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }
        if(expr instanceof ExprBinary)
        {
            ExprBinary.Op multiplicityOperator = ((ExprBinary) expr).op;
            switch (multiplicityOperator)
            {
                case ARROW              :
                case ANY_ARROW_SOME     :
                case ANY_ARROW_ONE      :
                case ANY_ARROW_LONE     :
                case SOME_ARROW_ANY     :
                case SOME_ARROW_SOME    :
                case SOME_ARROW_ONE     :
                case SOME_ARROW_LONE    :
                case ONE_ARROW_ANY      :
                case ONE_ARROW_SOME     :
                case ONE_ARROW_ONE      :
                case ONE_ARROW_LONE     :
                case LONE_ARROW_ANY     :
                case LONE_ARROW_SOME    :
                case LONE_ARROW_ONE     :
                case LONE_ARROW_LONE    :
                {
                    VariableDeclaration declaration = new VariableDeclaration(variableName, setSort, null);
                    Expression subset = BinaryExpression.Op.SUBSET.make(declaration.getVariable(), range);
                    declaration.setConstraint(subset);
                    return declaration;
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }
        throw new UnsupportedOperationException();
    }

    private VariableDeclaration getVariableDeclaration(String variableName, SetSort setSort, Expression range)
    {
        VariableDeclaration declaration = new VariableDeclaration(variableName, setSort.elementSort, null);
        Expression member = BinaryExpression.Op.MEMBER.make(declaration.getVariable(), range);
        declaration.setConstraint(member);
        return declaration;
    }

    private Expression getMultiplicityConstraint(Expr expr, VariableDeclaration variable, SetSort setSort)
    {
        if(expr instanceof ExprUnary)
        {
            ExprUnary.Op multiplicityOperator = ((ExprUnary) expr).op;
            Expression emptySet = UnaryExpression.Op.EMPTYSET.make(setSort);
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
                    Expression empty = BinaryExpression.Op.EQ.make(variable.getVariable(), emptySet);
                    Expression notEmpty = UnaryExpression.Op.NOT.make(empty);
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
                    Expression empty = BinaryExpression.Op.EQ.make(variable.getVariable(), emptySet);
                    VariableDeclaration singleElement = new VariableDeclaration(TranslatorUtils.getNewAtomName(), setSort.elementSort, null);
                    Expression singleton = UnaryExpression.Op.SINGLETON.make(singleElement.getVariable());
                    Expression isSingleton = BinaryExpression.Op.EQ.make(variable.getVariable(), singleton);
                    Expression emptyOrSingleton = BinaryExpression.Op.OR.make(empty, isSingleton);
                    Expression exists = QuantifiedExpression.Op.EXISTS.make(emptyOrSingleton, singleElement);
                    return exists;
                }
                default:
                    throw new UnsupportedOperationException();
            }
        }
        if(expr instanceof ExprBinary)
        {
            return BoolConstant.True;
        }
        throw new UnsupportedOperationException();
    }

    private Expression translateAllQuantifier(Expression body, Map<String, Expression> ranges,
                                              Environment environment, Expression multiplicityConstraints)
    {
        // all x: e1, y: e2, ... | f is translated into
        // forall x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints implies f)


        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression memberOrSubset = getMemberOrSubsetExpressions(ranges, environment);
        Expression and = BinaryExpression.Op.AND.make(memberOrSubset, multiplicityConstraints);
        Expression implies = BinaryExpression.Op.IMPLIES.make(and, body);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, quantifiedVariables);
        return forAll;
    }

    private Expression translateNoQuantifier(Expression body, Map<String, Expression> ranges,
                                             Environment environment, Expression multiplicityConstraints)
    {
        Expression notBody = UnaryExpression.Op.NOT.make(body);
        return translateAllQuantifier(notBody, ranges, environment, multiplicityConstraints);
    }

    private Expression translateSomeQuantifier(Expression body, Map<String, Expression> ranges,
                                               Environment environment, Expression multiplicityConstraints)
    {

        // some x: e1, y: e2, ... | f is translated into
        // exists x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints and f)

        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression and = getMemberOrSubsetExpressions(ranges, environment);
        and = BinaryExpression.Op.AND.make(and, multiplicityConstraints);
        and = BinaryExpression.Op.AND.make(and, body);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(and, quantifiedVariables);
        return exists;
    }

    private Expression getMemberOrSubsetExpressions(Map<String, Expression> ranges, Environment environment)
    {
        Expression and = BoolConstant.True;
        for (Map.Entry<String, Expression> entry : ranges.entrySet())
        {
            VariableDeclaration variable = (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration();
            Expression memberOrSubset;
            if (variable.getSort() instanceof TupleSort)
            {
                memberOrSubset = BinaryExpression.Op.MEMBER.make(variable.getVariable(), entry.getValue());
            }
            else if (variable.getSort() instanceof SetSort)
            {
                memberOrSubset = BinaryExpression.Op.SUBSET.make(variable.getVariable(), entry.getValue());
            }
            else
            {
                throw new UnsupportedOperationException(variable.getSort().toString());
            }
            and = BinaryExpression.Op.AND.make(and, memberOrSubset);
        }
        return and;
    }

    private Expression translateOneQuantifier(Expression body, Map<String, Expression> ranges,
                                              Environment environment, Expression multiplicityConstraints)
    {
        // one x: e1, y: e2, ... | f(x, y, ...) is translated into
        // exists x, y, ... ( x in e1 and y in e2 and ... and multiplicityConstraints(x, y, ...) and f(x, y, ...) and
        //                      for all x', y', ... (x in e1 and y in e2 ... and multiplicityConstraints(x', y', ...)
        //                              and not (x' = x and y' = y ...) implies not f(x', y', ...)))

        List<VariableDeclaration> oldVariables = ranges.entrySet()
                                                            .stream()
                                                            .map(entry -> (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration())
                                                            .collect(Collectors.toList());

        Expression oldMemberOrSubset = getMemberOrSubsetExpressions(ranges, environment);

        Expression existsAnd = BinaryExpression.Op.AND.make(oldMemberOrSubset, multiplicityConstraints);

        existsAnd = BinaryExpression.Op.AND.make(existsAnd, body);

        List<VariableDeclaration> newVariables = new ArrayList<>();

        Expression newBody = body;
        Expression oldEqualNew = BoolConstant.True;
        Expression newMemberOrSubset = BoolConstant.True;
        Expression newMultiplicityConstraints = multiplicityConstraints;
        for (Map.Entry<String, Expression> entry : ranges.entrySet())
        {
            VariableDeclaration oldVariable = (VariableDeclaration) ((Variable) environment.get(entry.getKey())).getDeclaration();
            VariableDeclaration newVariable = new VariableDeclaration(TranslatorUtils.getNewAtomName(), oldVariable.getSort(), null);
            if(oldVariable.getConstraint() != null)
            {
                Expression newConstraint = oldVariable.getConstraint().substitute(oldVariable.getVariable(), newVariable.getVariable());
                newVariable.setConstraint(newConstraint);
            }

            newVariables.add(newVariable);
            newBody = newBody.substitute(oldVariable.getVariable(), newVariable.getVariable());
            newMultiplicityConstraints = newMultiplicityConstraints.substitute(oldVariable.getVariable(), newVariable.getVariable());

            oldEqualNew = BinaryExpression.Op.AND.make(oldEqualNew, BinaryExpression.Op.EQ.make(oldVariable.getVariable(), newVariable.getVariable()));
            if (newVariable.getSort() instanceof TupleSort)
            {
                newMemberOrSubset = BinaryExpression.Op.AND.make(newMemberOrSubset, BinaryExpression.Op.MEMBER.make(newVariable.getVariable(), entry.getValue()));
            }
            else if (newVariable.getSort() instanceof SetSort)
            {
                newMemberOrSubset = BinaryExpression.Op.AND.make(newMemberOrSubset, BinaryExpression.Op.SUBSET.make(newVariable.getVariable(), entry.getValue()));
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }


        newBody = UnaryExpression.Op.NOT.make(newBody);
        Expression notOldEqualNew = UnaryExpression.Op.NOT.make(oldEqualNew);

        Expression forAllAnd = BinaryExpression.Op.AND.make(newMemberOrSubset, newMultiplicityConstraints);
        forAllAnd = BinaryExpression.Op.AND.make(forAllAnd, notOldEqualNew);

        Expression implies = BinaryExpression.Op.IMPLIES.make(forAllAnd, newBody);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies,  newVariables);
        existsAnd = BinaryExpression.Op.AND.make(existsAnd, forAll);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(existsAnd, oldVariables);
        return exists;
    }

    private Expression translateLoneQuantifier(Expression body, Map<String, Expression> ranges,
                                                         Environment environment, Expression multiplicityConstraints)
    {
        // lone ... | f is translated into
        // (all ... | not f)  or (one ... | f)

        Expression notBody = UnaryExpression.Op.NOT.make(body);
        Expression allNot = translateAllQuantifier(notBody, ranges, environment, multiplicityConstraints);
        Expression one = translateOneQuantifier(body, ranges, environment, multiplicityConstraints);
        Expression or = BinaryExpression.Op.OR.make(allNot, one);
        return or;
    }
}
