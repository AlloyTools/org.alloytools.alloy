package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
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
        Map<String, Expression> ranges = new HashMap<>();
        for (Decl decl: exprQt.decls)
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
                    return translateAllFirstOrderQuantifier(body, ranges, newVariableScope);
                case NO:
                    return translateNoFirstOrderQuantifier(body, ranges, newVariableScope);
                case SOME:
                    return translateSomeFirstOrderQuantifier(body, ranges, newVariableScope);
                case ONE:
//                    return translateOneFirstOrderQuantifier(name, body, ranges, newVariableScope);
                case LONE:
//                    return translateLoneFirstOrderQuantifier(name, body, ranges, newVariableScope);
                case COMPREHENSION:
                    throw new UnsupportedOperationException();
                default:
                    throw new UnsupportedOperationException();
        }
//        throw new UnsupportedOperationException();
    }

    private Expression translateAllFirstOrderQuantifier(Expression body, Map<String, Expression> ranges,
                                                        Map<String, Expression> variablesScope)
    {
        // all x: e1, y: e2, ... | f is translated into
        // forall x, y,... (x in e1 and y in e2 and ... implies f)


        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
                                                              .stream()
                                                              .map(entry -> (VariableDeclaration)((Variable) variablesScope.get(entry.getKey())).getDeclaration())
                                                              .collect(Collectors.toList());

        Expression and = getMemberOrSubsetExpressions(ranges, variablesScope);

        Expression implies = new BinaryExpression(and, BinaryExpression.Op.IMPLIES, body);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, quantifiedVariables, implies);
        return forAll;
    }

    private Expression translateNoFirstOrderQuantifier(Expression body, Map<String, Expression> ranges,
                                                       Map<String, Expression> variablesScope)
    {
        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        return translateAllFirstOrderQuantifier(notBody, ranges, variablesScope);
    }

    private Expression translateSomeFirstOrderQuantifier(Expression body, Map<String, Expression> ranges,
                                                         Map<String, Expression> variablesScope)
    {

        // some x: e1, y: e2, ... | f is translated into
        // exists x, y,... (x in e1 and y in e2 and ... and f)

        List<VariableDeclaration> quantifiedVariables = ranges.entrySet()
              .stream()
              .map(entry -> (VariableDeclaration)((Variable) variablesScope.get(entry.getKey())).getDeclaration())
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

    private Expression translateOneFirstOrderQuantifier(ExprHasName name, Expression body, Map<String, Expression> ranges,
                                                        Map<String, Expression> variablesScope)
    {
        // some x: e | f(x) is translated into
        // exists x . x in e and f and for all y . y in e and y != x implies not f(y)
        VariableDeclaration x = (VariableDeclaration)((Variable)variablesScope.get(name.label)).getDeclaration();
        Expression xMember = new BinaryExpression(x.getVariable(), BinaryExpression.Op.MEMBER, ranges.get(name.label));

        VariableDeclaration y = new VariableDeclaration(TranslatorUtils.getNewAtomName(), x.getSort());
        Expression yMember = new BinaryExpression(y.getVariable(), BinaryExpression.Op.MEMBER, ranges.get(name.label));
        Expression yEqualX = new BinaryExpression(y.getVariable(), BinaryExpression.Op.EQ, x.getVariable());
        Expression notYEqualX = new UnaryExpression(UnaryExpression.Op.NOT, yEqualX);
        Expression yBody = body.substitute(x.getVariable(), y.getVariable());
        Expression notYBody = new UnaryExpression(UnaryExpression.Op.NOT, yBody);
        Expression and1 = new BinaryExpression(yMember,BinaryExpression.Op.AND, notYEqualX);
        Expression implies = new BinaryExpression(and1,BinaryExpression.Op.IMPLIES, notYBody);
        Expression forAll = new QuantifiedExpression(QuantifiedExpression.Op.FORALL, implies, y);
        Expression and2 = new BinaryExpression(body, BinaryExpression.Op.AND, forAll);
        Expression and3 = new BinaryExpression(xMember, BinaryExpression.Op.AND, and2);
        Expression exists = new QuantifiedExpression(QuantifiedExpression.Op.EXISTS, and3, x);
        return exists;
    }

    private Expression translateLoneFirstOrderQuantifier(ExprHasName name, Expression body, Map<String, Expression> ranges,
                                                         Map<String, Expression> variablesScope)
    {
        // lone x: e | f is translated into
        // (all x: e | not f)  or (one x: e | f)

        Expression notBody = new UnaryExpression(UnaryExpression.Op.NOT, body);
        Expression allNot = translateAllFirstOrderQuantifier(notBody, ranges, variablesScope);
        Expression one = translateOneFirstOrderQuantifier(name, body, ranges, variablesScope);
        Expression or = new BinaryExpression(allNot, BinaryExpression.Op.OR, one);
        return or;
    }
}
