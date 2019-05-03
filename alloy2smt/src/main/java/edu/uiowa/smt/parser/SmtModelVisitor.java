/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.parser;

import edu.uiowa.smt.smtAst.*;
import edu.uiowa.smt.parser.antlr.SmtBaseVisitor;
import edu.uiowa.smt.parser.antlr.SmtParser;
import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class SmtModelVisitor extends SmtBaseVisitor<SmtAst>
{
    private Map<String, Variable> environment = new HashMap<>();

    @Override
    public SmtAst visitModel(SmtParser.ModelContext ctx)
    {
        SmtModel model = new SmtModel();

        for (SmtParser.SortDeclarationContext context: ctx.sortDeclaration())
        {
            model.addSort((Sort) this.visitSortDeclaration(context));
        }

        for (SmtParser.FunctionDefinitionContext context: ctx.functionDefinition())
        {
            FunctionDefinition definition = (FunctionDefinition) this.visitFunctionDefinition(context);
            model.addFunction(definition);
            if(definition.getInputVariables().size() == 0)
            {
                environment.put(definition.getName(), definition.getVariable());
            }
            //ToDo: handle functions and lambda expressions
        }

        return model;
    }

    @Override
    public SmtAst visitSortDeclaration(SmtParser.SortDeclarationContext ctx)
    {
        String  sortName    = ctx.sortName().getText();
        int     arity       = Integer.parseInt(ctx.arity().getText());
        Sort    sort        = new Sort(sortName, arity);
        return sort;
    }

    @Override
    public SmtAst visitSort(SmtParser.SortContext ctx)
    {
        if(ctx.sortName() != null)
        {
            switch (ctx.sortName().getText())
            {
                case AbstractTranslator.atom: return AbstractTranslator.atomSort;
                case AbstractTranslator.intSortName: return AbstractTranslator.intSort;
                case AbstractTranslator.uninterpretedIntName: return AbstractTranslator.uninterpretedInt;
                default:
                    throw new UnsupportedOperationException(String.format("Unknown sort '%s'", ctx.sortName().getText()));
            }
        }

        if(ctx.tupleSort() != null)
        {
            return this.visitTupleSort(ctx.tupleSort());
        }

        if(ctx.setSort() != null)
        {
            return this.visitSetSort(ctx.setSort());
        }
        throw new UnsupportedOperationException();
    }

    @Override
    public SmtAst visitTupleSort(SmtParser.TupleSortContext ctx)
    {
        List<Sort> sorts    = new ArrayList<>(ctx.sort().size());

        for (SmtParser.SortContext sortContext: ctx.sort())
        {
            Sort sort = (Sort) this.visitSort(sortContext);
            sorts.add(sort);
        }

        return new TupleSort(sorts);
    }

    @Override
    public SmtAst visitSetSort(SmtParser.SetSortContext ctx)
    {
        Sort elementSort = (Sort) this.visitSort(ctx.sort());
        return new SetSort(elementSort);
    }

    @Override
    public SmtAst visitFunctionDefinition(SmtParser.FunctionDefinitionContext ctx)
    {
        String name = ctx.functionName().getText();

        List<VariableDeclaration> arguments   = ctx.argument().stream()
                                                   .map(argument -> (VariableDeclaration) this.visitArgument(argument))
                                                   .collect(Collectors.toList());

        Sort returnSort = (Sort) visitSort(ctx.sort());

        Map<String, Variable> functionArguments = arguments
                .stream()
                .collect(Collectors
                        .toMap(v -> v.getName(), v -> v.getVariable()));

        Expression expression = (Expression) this.visitExpression(ctx.expression(), functionArguments);

        FunctionDefinition definition   = new FunctionDefinition(name, arguments, returnSort,  expression);

        return definition;
    }

    @Override
    public SmtAst visitArgument(SmtParser.ArgumentContext ctx)
    {
        String argumentName = ctx.argumentName().getText();
        Sort   argumentSort = (Sort) this.visitSort(ctx.sort());
        return new VariableDeclaration(argumentName, argumentSort);
    }

    public SmtAst visitExpression(SmtParser.ExpressionContext ctx, Map<String, Variable> arguments)
    {
        if(ctx.constant() != null)
        {
            return this.visitConstant(ctx.constant());
        }
        if(ctx.variable() != null)
        {
            return this.visitVariable(ctx.variable(), arguments);
        }
        if(ctx.unaryExpression() != null)
        {
            return this.visitUnaryExpression(ctx.unaryExpression(), arguments);
        }
        if(ctx.binaryExpression() != null)
        {
            return this.visitBinaryExpression(ctx.binaryExpression(), arguments);
        }
        if(ctx.ternaryExpression() != null)
        {
            return this.visitTernaryExpression(ctx.ternaryExpression(), arguments);
        }
        if(ctx.multiArityExpression() != null)
        {
            return this.visitMultiArityExpression(ctx.multiArityExpression(), arguments);
        }
        if(ctx.expression() != null)
        {
            return this.visitExpression(ctx.expression(), arguments);
        }

        throw new UnsupportedOperationException();
    }

    public SmtAst visitUnaryExpression(SmtParser.UnaryExpressionContext ctx,
                                       Map<String, Variable> arguments)
    {
        Expression expression       = (Expression) this.visitExpression(ctx.expression(), arguments);
        UnaryExpression.Op operator = UnaryExpression.Op.getOp(ctx.UnaryOperator().getText());
        return new UnaryExpression(operator, expression);
    }

    public SmtAst visitBinaryExpression(SmtParser.BinaryExpressionContext ctx, Map<String, Variable> arguments)
    {
        Expression left   = (Expression) this.visitExpression(ctx.expression(0), arguments);
        Expression right  = (Expression) this.visitExpression(ctx.expression(1), arguments);

        BinaryExpression.Op operator = BinaryExpression.Op.getOp(ctx.BinaryOperator().getText());
        return new BinaryExpression(left, operator, right);
    }

    public SmtAst visitTernaryExpression(SmtParser.TernaryExpressionContext ctx, Map<String, Variable> arguments)
    {
        List<Expression> expressions = ctx.expression().stream()
                                          .map(expression -> (Expression) this.visitExpression(expression, arguments))
                                          .collect(Collectors.toList());

        return new ITEExpression(expressions.get(0), expressions.get(1), expressions.get(2));
    }

    public SmtAst visitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx, Map<String, Variable> arguments)
    {
        List<Expression> expressions = ctx.expression().stream()
                                          .map(expression -> (Expression) this.visitExpression(expression, arguments))
                                          .collect(Collectors.toList());

        MultiArityExpression.Op operator = MultiArityExpression.Op.getOp(ctx.MultiArityOperator().getText());
        return new MultiArityExpression(operator, expressions);
    }

    @Override
    public SmtAst visitConstant(SmtParser.ConstantContext ctx)
    {
        if(ctx.boolConstant() != null)
        {
            return this.visitBoolConstant(ctx.boolConstant());
        }
        if(ctx.integerConstant() != null)
        {
            return this.visitIntegerConstant(ctx.integerConstant());
        }
        if(ctx.uninterpretedConstant() != null)
        {
            return this.visitUninterpretedConstant(ctx.uninterpretedConstant());
        }
        if(ctx.emptySet() != null)
        {
            return this.visitEmptySet(ctx.emptySet());
        }
        throw new UnsupportedOperationException();
    }

    @Override
    public SmtAst visitBoolConstant(SmtParser.BoolConstantContext ctx)
    {
        if(ctx.True() != null)
        {
            return new BoolConstant(true);
        }
        else
        {
            return new BoolConstant(false);
        }
    }

    @Override
    public SmtAst visitIntegerConstant(SmtParser.IntegerConstantContext ctx)
    {
        int constant = Integer.parseInt(ctx.getText());
        return IntConstant.getInstance(constant);
    }

    @Override
    public SmtAst visitUninterpretedConstant(SmtParser.UninterpretedConstantContext ctx)
    {
        if(ctx.AtomPrefix() != null)
        {
            return new UninterpretedConstant(ctx.getText(), AbstractTranslator.atomSort);
        }
        if(ctx.UninterpretedIntPrefix() != null)
        {
            return new UninterpretedConstant(ctx.getText(), AbstractTranslator.uninterpretedInt);
        }
        throw new UnsupportedOperationException(String.format("Unknown constant value '%s'", ctx.getText()));
    }

    @Override
    public SmtAst visitEmptySet(SmtParser.EmptySetContext ctx)
    {
        Sort elementSort = (Sort) this.visitSort(ctx.sort());
        Sort setSort = new SetSort(elementSort);
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, setSort);
    }

    public SmtAst visitVariable(SmtParser.VariableContext ctx, Map<String, Variable> arguments)
    {
        String variableName = ctx.getText();
        if(!arguments.containsKey(variableName))
        {
            throw new RuntimeException(String.format("The variable '%s' is undefined", variableName));
        }
        Expression variable = arguments.get(ctx.getText());
        return variable;
    }

    @Override
    public SmtAst visitGetValue(SmtParser.GetValueContext ctx)
    {
        List<ExpressionValue> values = new ArrayList<>();

        for(int i = 0; i < ctx.expression().size() ; i = i + 2)
        {
            Expression expression = (Expression) visitExpression(ctx.expression(i), environment);
            Expression value = (Expression) visitExpression(ctx.expression(i + 1), environment);
            ExpressionValue expressionValue = new ExpressionValue(expression, value);
            values.add(expressionValue);
        }

        return new SmtValues(values);
    }

    @Override
    public SmtAst visitExpression(SmtParser.ExpressionContext ctx)
    {
        throw new UnsupportedOperationException("Use the overloaded method visitExpression(SmtParser.ExpressionContext ctx, Map<String, Variable> arguments)");
    }
}