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

        Expression expression = (Expression) this.visitTerm(ctx.term());

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

    @Override
    public SmtAst visitIntegerConstant(SmtParser.IntegerConstantContext ctx)
    {
        int constant = Integer.parseInt(ctx.getText());
        return new IntConstant(constant);
    }

    @Override
    public SmtAst visitTupleConstant(SmtParser.TupleConstantContext ctx)
    {
        List<Expression> expressions = ctx.term().stream()
                .map(term -> (Expression) this.visitTerm(term))
                .collect(Collectors.toList());

        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
    }

    @Override
    public SmtAst visitSingletonConstant(SmtParser.SingletonConstantContext ctx)
    {
        Expression expression = (Expression) this.visitTerm(ctx.term());
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, expression);
    }

    @Override
    public SmtAst visitUnionConstant(SmtParser.UnionConstantContext ctx)
    {
        Expression left  = (Expression) this.visitTerm(ctx.term(0));
        Expression right = (Expression) this.visitTerm(ctx.term(1));

        return new BinaryExpression(left, BinaryExpression.Op.UNION, right);
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