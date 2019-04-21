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
import java.util.List;
import java.util.stream.Collectors;

public class SmtModelVisitor extends SmtBaseVisitor<SmtAst>
{
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
            model.addFunction((FunctionDefinition) this.visitFunctionDefinition(context));
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

        List<VariableDeclaration>  arguments   = ctx.argument().stream()
            .map(argument -> (VariableDeclaration) this.visitArgument(argument))
            .collect(Collectors.toList());

        Sort returnSort = (Sort) visitSort(ctx.sort());

        Expression expression = (Expression) this.visitExpression(ctx.expression(), arguments);

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

    public SmtAst visitExpression(SmtParser.ExpressionContext ctx, List<VariableDeclaration>  arguments)
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
                                       List<VariableDeclaration>  arguments)
    {
        Expression expression       = (Expression) this.visitExpression(ctx.expression(), arguments);
        UnaryExpression.Op operator = UnaryExpression.Op.getOp(ctx.UnaryOperator().getText());
        return new UnaryExpression(operator, expression);
    }

    public SmtAst visitBinaryExpression(SmtParser.BinaryExpressionContext ctx, List<VariableDeclaration>  arguments)
    {
        Expression left   = (Expression) this.visitExpression(ctx.expression(0), arguments);
        Expression right  = (Expression) this.visitExpression(ctx.expression(1), arguments);

        BinaryExpression.Op operator = BinaryExpression.Op.getOp(ctx.BinaryOperator().getText());
        return new BinaryExpression(left, operator, right);
    }

    public SmtAst visitTernaryExpression(SmtParser.TernaryExpressionContext ctx, List<VariableDeclaration>  arguments)
    {
        List<Expression> expressions = ctx.expression().stream()
                .map(expression -> (Expression) this.visitExpression(expression, arguments))
                .collect(Collectors.toList());

        return new ITEExpression(expressions.get(0), expressions.get(1), expressions.get(2));
    }

    public SmtAst visitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx, List<VariableDeclaration>  arguments)
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
        Sort sort = (Sort) this.visitSort(ctx.sort());
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, sort);
    }

    public SmtAst visitVariable(SmtParser.VariableContext ctx, List<VariableDeclaration>  arguments)
    {
        Expression variable = arguments.stream()
                .filter(argument -> argument.getName().equals(ctx.getText()))
                .findFirst().get().getVariable();
        return variable;
    }
}