package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
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

    Expression translateExprQt(ExprQt exprQt, Map<String, Expression> variableScope)
    {
        // create a new scope for quantified variables
        Map<String, Expression> newVariableScope = new HashMap<>(variableScope);
        Map<String, Expression> ranges = new LinkedHashMap<>();

        // this variable maintains the multiplicity constraints for declared variables
        // x: [one, lone, some, set] e
        Expression multiplicityConstraints = new BoolConstant(true);
        for (Decl decl : exprQt.decls)
        {
            Expression range = exprTranslator.translateExpr(decl.expr, newVariableScope);
            for (ExprHasName name : decl.names)
            {
                ranges.put(name.label, range);
                String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                SetSort setSort = (SetSort) range.getSort();
                VariableDeclaration variable;
                ExprUnary.Op multiplicityOperator = ((ExprUnary) decl.expr).op;
                variable = getVariableDeclaration(multiplicityOperator, sanitizedName, setSort);
                Expression constraint = getMultiplicityConstraint(multiplicityOperator, variable, setSort);
                multiplicityConstraints = new BinaryExpression(multiplicityConstraints, BinaryExpression.Op.AND, constraint);
                newVariableScope.put(name.label, variable.getVariable());
            }
        }

        // translate the body of the quantified expression
        Expression body = exprTranslator.translateExpr(exprQt.sub, newVariableScope);

        switch (exprQt.op)
        {
            case ALL:
                return translateAllQuantifier(body, ranges, newVariableScope, multiplicityConstraints);
            case NO:
                return translateNoQuantifier(body, ranges, newVariableScope, multiplicityConstraints);
            case SOME:
                return translateSomeQuantifier(body, ranges, newVariableScope, multiplicityConstraints);
            case ONE:
                    return translateOneQuantifier(body, ranges, newVariableScope, multiplicityConstraints);
            case LONE:
                    return translateLoneQuantifier(body, ranges, newVariableScope, multiplicityConstraints);
            case COMPREHENSION:
                throw new UnsupportedOperationException();
            default:
                throw new UnsupportedOperationException();
        }
//        throw new UnsupportedOperationException();
    }

    private VariableDeclaration getVariableDeclaration(ExprUnary.Op multiplicityOperator, String variableName, SetSort setSort)
    {
        VariableDeclaration variable;
        switch (multiplicityOperator)
        {
            case NOOP: // same as ONEOF
            case ONEOF:
            {
                variable = new VariableDeclaration(variableName, setSort.elementSort);
                break;
            }
            case SOMEOF: // same as SETOF
            case LONEOF: // same as SETOF
            case SETOF:
            {
                variable = new VariableDeclaration(variableName, setSort);
                break;
            }
            default:
                throw new UnsupportedOperationException();
        }
        return variable;
    }

    private Expression getMultiplicityConstraint(ExprUnary.Op multiplicityOperator, VariableDeclaration variable, SetSort setSort)
    {
        Expression emptySet = new UnaryExpression(UnaryExpression.Op.EMPTYSET, setSort);
        switch (multiplicityOperator)
        {
            case NOOP: // same as ONEOF
            case ONEOF:
            {
                // variable.getSort() is a tuple sort, so there is no constraint
                return new BoolConstant(true);
            }
            case SOMEOF:
            {
                // the set is not empty
                Expression empty = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ, emptySet);
                Expression notEmpty = new UnaryExpression(UnaryExpression.Op.NOT, empty);
                return notEmpty;
            }
            case SETOF:
            {
                // variable.getSort() is a set, so there is no constraint
                return new BoolConstant(true);
            }
            case LONEOF:
            {
                // either the set is empty or a singleton
                Expression empty = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ, emptySet);
                VariableDeclaration singleElement = new VariableDeclaration(TranslatorUtils.getNewAtomName(), setSort.elementSort);
                Expression singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, singleElement.getVariable());
                Expression isSingleton = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.EQ, singleton);
                Expression emptyOrSingleton = new BinaryExpression(empty, BinaryExpression.Op.OR, isSingleton);
                Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, emptyOrSingleton, singleElement);
                return exists;
            }
            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expression translateAllQuantifier(Expression body, Map<String, Expression> ranges,
                                              Map<String, Expression> variablesScope, Expression multiplicityConstraints)
    {
        // all x: e1, y: e2, ... | f is translated into
        // forall x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints implies f)


        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression memberOrSubset = getMemberOrSubsetExpressions(ranges, variablesScope);
        Expression and = new BinaryExpression(memberOrSubset, BinaryExpression.Op.AND, multiplicityConstraints);
        Expression implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, body);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, quantifiedVariables, implies);
        return forAll;
    }

    private Expression translateNoQuantifier(Expression body, Map<String, Expression> ranges,
                                             Map<String, Expression> variablesScope, Expression multiplicityConstraints)
    {
        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        return translateAllQuantifier(notBody, ranges, variablesScope, multiplicityConstraints);
    }

    private Expression translateSomeQuantifier(Expression body, Map<String, Expression> ranges,
                                               Map<String, Expression> variablesScope, Expression multiplicityConstraints)
    {

        // some x: e1, y: e2, ... | f is translated into
        // exists x, y,... (x in e1 and y in e2 and ... and multiplicityConstraints and f)

        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression and = getMemberOrSubsetExpressions(ranges, variablesScope);
        and = new BinaryExpression(and, BinaryExpression.Op.AND, multiplicityConstraints);
        and = new BinaryExpression(and, BinaryExpression.Op.AND, body);
        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, quantifiedVariables, and);
        return exists;
    }

    private Expression getMemberOrSubsetExpressions(Map<String, Expression> ranges, Map<String, Expression> variablesScope)
    {
        Expression and = new BoolConstant(true);
        for (Map.Entry<String, Expression> entry : ranges.entrySet())
        {
            VariableDeclaration variable = (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration();
            Expression memberOrSubset;
            if (variable.getSort() instanceof TupleSort)
            {
                memberOrSubset = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.MEMBER, entry.getValue());
            }
            else if (variable.getSort() instanceof SetSort)
            {
                memberOrSubset = new BinaryExpression(variable.getVariable(), BinaryExpression.Op.SUBSET, entry.getValue());
            }
            else
            {
                throw new UnsupportedOperationException(variable.getSort().toString());
            }
            and = new BinaryExpression(and, BinaryExpression.Op.AND, memberOrSubset);
        }
        return and;
    }

    private Expression translateOneQuantifier(Expression body, Map<String, Expression> ranges,
                                              Map<String, Expression> variablesScope, Expression multiplicityConstraints)
    {
        // one x: e1, y: e2, ... | f(x, y, ...) is translated into
        // exists x, y, ... ( x in e1 and y in e2 and ... and multiplicityConstraints(x, y, ...) and f(x, y, ...) and
        //                      for all x', y', ... (x in e1 and y in e2 ... and multiplicityConstraints(x', y', ...)
        //                              and not (x' = x and y' = y ...) implies not f(x', y', ...)))

        List<VariableDeclaration> oldVariables = ranges.entrySet()
                                                            .stream()
                                                            .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                            .collect(Collectors.toList());

        Expression oldMemberOrSubset = getMemberOrSubsetExpressions(ranges, variablesScope);

        Expression existsAnd = new BinaryExpression(oldMemberOrSubset, BinaryExpression.Op.AND, multiplicityConstraints);

        existsAnd = new BinaryExpression(existsAnd, BinaryExpression.Op.AND, body);

        List<VariableDeclaration> newVariables = new ArrayList<>();

        Expression newBody = body;
        Expression oldEqualNew = new BoolConstant(true);
        Expression newMemberOrSubset = new BoolConstant(true);
        Expression newMultiplicityConstraints = multiplicityConstraints;
        for (Map.Entry<String, Expression> entry : ranges.entrySet())
        {
            VariableDeclaration oldVariable = (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration();
            VariableDeclaration newVariable = new VariableDeclaration(TranslatorUtils.getNewAtomName(), oldVariable.getSort());
            newVariables.add(newVariable);
            newBody = newBody.substitute(oldVariable.getVariable(), newVariable.getVariable());
            newMultiplicityConstraints = newMultiplicityConstraints.substitute(oldVariable.getVariable(), newVariable.getVariable());

            oldEqualNew = new BinaryExpression(oldEqualNew, BinaryExpression.Op.AND,
                    new BinaryExpression(oldVariable.getVariable(), BinaryExpression.Op.EQ, newVariable.getVariable()));
            if (newVariable.getSort() instanceof TupleSort)
            {
                newMemberOrSubset = new BinaryExpression(newMemberOrSubset, BinaryExpression.Op.AND,
                        new BinaryExpression(newVariable.getVariable(), BinaryExpression.Op.MEMBER, entry.getValue()));
            }
            else if (newVariable.getSort() instanceof SetSort)
            {
                newMemberOrSubset = new BinaryExpression(newMemberOrSubset, BinaryExpression.Op.AND,
                        new BinaryExpression(newVariable.getVariable(), BinaryExpression.Op.SUBSET, entry.getValue()));
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }


        newBody = new UnaryExpression(UnaryExpression.Op.NOT, newBody);
        Expression notOldEqualNew = new UnaryExpression(UnaryExpression.Op.NOT, oldEqualNew);

        Expression forAllAnd = new BinaryExpression(newMemberOrSubset, BinaryExpression.Op.AND, newMultiplicityConstraints);
        forAllAnd = new BinaryExpression(forAllAnd, BinaryExpression.Op.AND, notOldEqualNew);

        Expression implies = new BinaryExpression(forAllAnd, BinaryExpression.Op.IMPLIES, newBody);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, newVariables, implies);
        existsAnd = new BinaryExpression(existsAnd, BinaryExpression.Op.AND, forAll);
        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, oldVariables, existsAnd);
        return exists;
    }

    private Expression translateLoneQuantifier(Expression body, Map<String, Expression> ranges,
                                                         Map<String, Expression> variablesScope, Expression multiplicityConstraints)
    {
        // lone ... | f is translated into
        // (all ... | not f)  or (one ... | f)

        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        Expression allNot = translateAllQuantifier(notBody, ranges, variablesScope, multiplicityConstraints);
        Expression one = translateOneQuantifier(body, ranges, variablesScope, multiplicityConstraints);
        Expression or = new BinaryExpression(allNot, BinaryExpression.Op.OR, one);
        return or;
    }
}
