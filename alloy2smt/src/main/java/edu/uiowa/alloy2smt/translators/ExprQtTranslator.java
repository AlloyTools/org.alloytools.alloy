package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprQt;
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
        for (Decl decl : exprQt.decls)
        {
            Expression range = exprTranslator.translateExpr(decl.expr, newVariableScope);
            for (ExprHasName name : decl.names)
            {
                ranges.put(name.label, range);
                String sanitizedName = TranslatorUtils.sanitizeName(name.label);
                SetSort setSort = (SetSort) range.getSort();
                VariableDeclaration variable = new VariableDeclaration(sanitizedName, setSort.elementSort);
                newVariableScope.put(name.label, variable.getVariable());
            }
        }

        // translate the body of the quantified expression
        Expression body = exprTranslator.translateExpr(exprQt.sub, newVariableScope);

        switch (exprQt.op)
        {
            case ALL:
                return translateAllQuantifier(body, ranges, newVariableScope);
            case NO:
                return translateNoQuantifier(body, ranges, newVariableScope);
            case SOME:
                return translateSomeQuantifier(body, ranges, newVariableScope);
            case ONE:
                    return translateOneQuantifier(body, ranges, newVariableScope);
            case LONE:
                    return translateLoneQuantifier(body, ranges, newVariableScope);
            case COMPREHENSION:
                throw new UnsupportedOperationException();
            default:
                throw new UnsupportedOperationException();
        }
//        throw new UnsupportedOperationException();
    }

    private Expression translateAllQuantifier(Expression body, Map<String, Expression> ranges,
                                              Map<String, Expression> variablesScope)
    {
        // all x: e1, y: e2, ... | f is translated into
        // forall x, y,... (x in e1 and y in e2 and ... implies f)


        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression and = getMemberOrSubsetExpressions(ranges, variablesScope);

        Expression implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, body);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, quantifiedVariables, implies);
        return forAll;
    }

    private Expression translateNoQuantifier(Expression body, Map<String, Expression> ranges,
                                             Map<String, Expression> variablesScope)
    {
        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        return translateAllQuantifier(notBody, ranges, variablesScope);
    }

    private Expression translateSomeQuantifier(Expression body, Map<String, Expression> ranges,
                                               Map<String, Expression> variablesScope)
    {

        // some x: e1, y: e2, ... | f is translated into
        // exists x, y,... (x in e1 and y in e2 and ... and f)

        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression and = getMemberOrSubsetExpressions(ranges, variablesScope);

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
                                                        Map<String, Expression> variablesScope)
    {
        // one x: e1, y: e2, ... | f(x, y, ...) is translated into
        // exists x, y, ... ( x in e1 and y in e2 and ... and f(x, y, ...) and
        //                      for all x', y', ... (x in e1 and y in e2 ...
        //                              and not (x' = x and y' = y ...) implies not f(x', y', ...)))

        List<VariableDeclaration> oldVariables = ranges.entrySet()
                                                            .stream()
                                                            .map(entry -> (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                            .collect(Collectors.toList());

        Expression oldMemberOrSubset = getMemberOrSubsetExpressions(ranges, variablesScope);

        Expression existsAnd = new BinaryExpression(oldMemberOrSubset, BinaryExpression.Op.AND, body);

        List<VariableDeclaration> newVariables = new ArrayList<>();

        Expression newBody = body;
        Expression oldEqualNew = new BoolConstant(true);
        Expression newMemberOrSubset = new BoolConstant(true);
        for (Map.Entry<String, Expression> entry : ranges.entrySet())
        {
            VariableDeclaration oldVariable = (VariableDeclaration) ((Variable) variablesScope.get(entry.getKey())).getDeclaration();
            VariableDeclaration newVariable = new VariableDeclaration(TranslatorUtils.getNewAtomName(), oldVariable.getSort());
            newVariables.add(newVariable);
            newBody = newBody.substitute(oldVariable.getVariable(), newVariable.getVariable());

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

        Expression forAllAnd = new BinaryExpression(newMemberOrSubset, BinaryExpression.Op.AND, notOldEqualNew);

        Expression implies = new BinaryExpression(forAllAnd, BinaryExpression.Op.IMPLIES, newBody);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, newVariables, implies);
        existsAnd = new BinaryExpression(existsAnd, BinaryExpression.Op.AND, forAll);
        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, oldVariables, existsAnd);
        return exists;
    }

    private Expression translateLoneQuantifier(Expression body, Map<String, Expression> ranges,
                                                         Map<String, Expression> variablesScope)
    {
        // lone ... | f is translated into
        // (all ... | not f)  or (one ... | f)

        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        Expression allNot = translateAllQuantifier(notBody, ranges, variablesScope);
        Expression one = translateOneQuantifier(body, ranges, variablesScope);
        Expression or = new BinaryExpression(allNot, BinaryExpression.Op.OR, one);
        return or;
    }
}
