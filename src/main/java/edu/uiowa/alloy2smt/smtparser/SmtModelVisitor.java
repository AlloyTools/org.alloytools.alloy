package edu.uiowa.alloy2smt.smtparser;

import edu.uiowa.alloy2smt.smtAst.*;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtBaseVisitor;
import edu.uiowa.alloy2smt.smtparser.antlr.SmtParser;

import java.util.List;
import java.util.stream.Collectors;

public class SmtModelVisitor extends SmtBaseVisitor<SMTAst>
{
    private SMTProgram model = new SMTProgram();

    public SMTProgram getModel()
    {
        return  model;
    }

    @Override
    public SMTAst visitSortDeclaration(SmtParser.SortDeclarationContext ctx)
    {
        String  sortName    = ctx.sortName().getText();
        int     arity       = Integer.parseInt(ctx.arity().getText());
        Sort    sort        = new Sort(sortName, arity);

        model.addSort(sort);
        return sort;
    }

    @Override
    public SMTAst visitSortName(SmtParser.SortNameContext ctx)
    {
        String  sortName    = ctx.getText();
        Sort    sort        = model.getSorts().stream()
                .filter(s -> sortName.equals(s.getName()))
                .findFirst()
                .orElse(null);
        if(sort == null)
        {
            sort = new Sort(sortName, 0);
            this.model.addSort(sort);
        }
        return sort;
    }

    @Override
    public SMTAst visitTupleSort(SmtParser.TupleSortContext ctx)
    {
        TupleSort tupleSort = new TupleSort();

        for (SmtParser.SortContext sortContext: ctx.sort())
        {
            Sort sort = (Sort) this.visitSort(sortContext);
            tupleSort.elementSorts.add(sort);
        }

        return tupleSort;
    }

    @Override
    public SMTAst visitSetSort(SmtParser.SetSortContext ctx)
    {
        Sort elementSort = (Sort) this.visitSort(ctx.sort());
        return new SetSort(elementSort);
    }

    @Override
    public SMTAst  visitFunctionDefinition(SmtParser.FunctionDefinitionContext ctx)
    {
        String name = ctx.functionName().getText();

        List<BoundVariableDeclaration>  arguments   = ctx.argument().stream()
            .map(argument -> (BoundVariableDeclaration) this.visitArgument(argument))
            .collect(Collectors.toList());

        Sort returnSort = (Sort) visitSort(ctx.sort());

        Expression expression = (Expression) this.visitTerm(ctx.term());

        FunctionDefinition definition   = new FunctionDefinition(name, arguments, returnSort,  expression);

        this.model.addFcnDef(definition);

        return definition;
    }

    @Override
    public SMTAst visitArgument(SmtParser.ArgumentContext ctx)
    {
        String argumentName = ctx.argumentName().getText();
        Sort   argumentSort = (Sort) this.visit(ctx.sort());
        return new BoundVariableDeclaration(argumentName, argumentSort);
    }

    @Override
    public SMTAst visitIntegerConstant(SmtParser.IntegerConstantContext ctx)
    {
        int constant = Integer.parseInt(ctx.getText());
        return new IntConstant(constant);
    }

    @Override
    public SMTAst visitTupleConstant(SmtParser.TupleConstantContext ctx)
    {
        List<Expression> expressions = ctx.term().stream()
                .map(term -> (Expression) this.visitTerm(term))
                .collect(Collectors.toList());

        return new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, expressions);
    }

    @Override
    public SMTAst visitSingletonConstant(SmtParser.SingletonConstantContext ctx)
    {
        Expression expression = (Expression) this.visitTerm(ctx.term());
        return new UnaryExpression(UnaryExpression.Op.SINGLETON, expression);
    }

    @Override
    public SMTAst visitUnionConstant(SmtParser.UnionConstantContext ctx)
    {
        Expression left  = (Expression) this.visitTerm(ctx.term(0));
        Expression right = (Expression) this.visitTerm(ctx.term(1));

        return new BinaryExpression(left, BinaryExpression.Op.UNION, right);
    }

    @Override
    public SMTAst visitAtomConstant(SmtParser.AtomConstantContext ctx)
    {
        return new AtomConstant(ctx.getText());
    }

    @Override
    public SMTAst visitEmptySet(SmtParser.EmptySetContext ctx)
    {
        Sort sort = (Sort) this.visitSort(ctx.sort());
        return new UnaryExpression(UnaryExpression.Op.EMPTYSET, sort);
    }
}