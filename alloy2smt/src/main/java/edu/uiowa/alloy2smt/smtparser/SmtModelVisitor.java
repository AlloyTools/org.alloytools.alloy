/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtparser;

import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtBaseVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;

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
            model.addFunctionDefinition((FunctionDefinition) this.visitFunctionDefinition(context));
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
            return new Sort(ctx.sortName().getText(), 0);
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

        List<BoundVariableDeclaration>  arguments   = ctx.argument().stream()
            .map(argument -> (BoundVariableDeclaration) this.visitArgument(argument))
            .collect(Collectors.toList());

        Sort returnSort = (Sort) visitSort(ctx.sort());

        Expression expression = (Expression) this.visitExpression(ctx.expression());

        FunctionDefinition definition   = new FunctionDefinition(name, arguments, returnSort,  expression);

        return definition;
    }

    @Override
    public SmtAst visitArgument(SmtParser.ArgumentContext ctx)
    {
        String argumentName = ctx.argumentName().getText();
        Sort   argumentSort = (Sort) this.visit(ctx.sort());
        return new BoundVariableDeclaration(argumentName, argumentSort);
    }

//    @Override
//    public SmtAst visitExpression(SmtParser.ExpressionContext ctx)
//    {
//        if(ctx.constant() != null)
//        {
//            return this.visitConstant(ctx.constant());
//        }
//        if(ctx.UnaryOperator() != null)
//        {
//            return this.visitUnaryOperator(ctx);
//        }
//
//    }

//    @Override
//    public SmtAst visitConstant(SmtParser.ConstantContext ctx)
//    {
//        if(ctx.integerConstant() != null)
//        {
//            return this.
//        }
//    }

    @Override
    public SmtAst visitIntegerConstant(SmtParser.IntegerConstantContext ctx)
    {
        int constant = Integer.parseInt(ctx.getText());
        return new IntConstant(constant);
    }

    @Override
    public SmtAst visitUnaryExpression(SmtParser.UnaryExpressionContext ctx)
    {
        Expression expression       = (Expression) this.visitExpression(ctx.expression());
        UnaryExpression.Op operator = UnaryExpression.Op.getOp(ctx.UnaryOperator().getText());
        return new UnaryExpression(operator, expression);
    }

    @Override
    public SmtAst visitBinaryExpression(SmtParser.BinaryExpressionContext ctx)
    {
        Expression left   = (Expression) this.visitExpression(ctx.expression(0));
        Expression right  = (Expression) this.visitExpression(ctx.expression(1));

        BinaryExpression.Op operator = BinaryExpression.Op.getOp(ctx.BinaryOperator().getText());
        return new BinaryExpression(left, operator, right);
    }

    @Override
    public SmtAst visitTernaryExpression(SmtParser.TernaryExpressionContext ctx)
    {
        List<Expression> expressions = ctx.expression().stream()
                .map(expression -> (Expression) this.visitExpression(expression))
                .collect(Collectors.toList());

        return new ITEExpression(expressions.get(0), expressions.get(1), expressions.get(2));
    }

    @Override
    public SmtAst visitMultiArityExpression(SmtParser.MultiArityExpressionContext ctx)
    {
        List<Expression> expressions = ctx.expression().stream()
                .map(expression -> (Expression) this.visitExpression(expression))
                .collect(Collectors.toList());

        MultiArityExpression.Op operator = MultiArityExpression.Op.getOp(ctx.MultiArityOperator().getText());
        return new MultiArityExpression(operator, expressions);
    }

    @Override
    public SmtAst visitAtomConstant(SmtParser.AtomConstantContext ctx)
    {
        return new AtomConstant(ctx.getText());
    }

    @Override
    public SmtAst visitEmptySet(SmtParser.EmptySetContext ctx)
    {
        Sort sort = (Sort) this.visitSort(ctx.sort());
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, sort);
    }
}