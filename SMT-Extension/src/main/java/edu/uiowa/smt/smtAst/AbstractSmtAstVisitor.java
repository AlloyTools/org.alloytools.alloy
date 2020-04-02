package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;

import java.util.Map;

abstract public class AbstractSmtAstVisitor implements SmtAstVisitor
{
    @Override
    public void visit(Expression expression)
    {
        if (expression instanceof Variable)
        {
            this.visit((Variable) expression);
        }
        else if (expression instanceof  UnaryExpression)
        {
            this.visit((UnaryExpression) expression);
        }
        else if (expression instanceof  BinaryExpression)
        {
            this.visit((BinaryExpression) expression);
        }
        else if (expression instanceof  MultiArityExpression)
        {
            this.visit((MultiArityExpression) expression);
        }
        else if (expression instanceof  QuantifiedExpression)
        {
            this.visit((QuantifiedExpression) expression);
        }
        else if (expression instanceof  Sort)
        {
            this.visit((Sort) expression);
        }
        else if (expression instanceof  IntConstant)
        {
            this.visit((IntConstant) expression);
        }
        else if (expression instanceof  FunctionCallExpression)
        {
            this.visit((FunctionCallExpression) expression);
        }
        else if (expression instanceof BoolConstant)
        {
            this.visit((BoolConstant) expression);
        }
        else if (expression instanceof  LetExpression)
        {
            this.visit((LetExpression) expression);
        }
        else if (expression instanceof  ITEExpression)
        {
            this.visit((ITEExpression) expression);
        }
        else if (expression instanceof UninterpretedConstant)
        {
            this.visit((UninterpretedConstant) expression);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public void visit(Sort sort)
    {
        if (sort instanceof  UninterpretedSort)
        {
            this.visit((UninterpretedSort) sort);
        }
        else if (sort instanceof  SetSort)
        {
            this.visit((SetSort) sort);
        }
        else if (sort instanceof  TupleSort)
        {
            this.visit((TupleSort) sort);
        }
        else if (sort instanceof  IntSort)
        {
            this.visit((IntSort) sort);
        }
        else if (sort instanceof  RealSort)
        {
            this.visit((RealSort) sort);
        }
        else if (sort instanceof  StringSort)
        {
            this.visit((StringSort) sort);
        }
        else if (sort instanceof  StringSort)
        {
            this.visit((StringSort) sort);
        }
        else if (sort instanceof  BoolSort)
        {
            this.visit((BoolSort) sort);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public void visit(SmtScript script)
    {
        for (Sort sort: script.getSorts())
        {
            visit(sort);
        }
        for (FunctionDeclaration function: script.getFunctions())
        {
            visit(function);
        }
        for (Assertion assertion: script.getAssertions())
        {
            visit(assertion);
        }
    }

    @Override
    public void visit(BinaryExpression expr)
    {
        visit(expr.getA());
        visit(expr.getB());
    }

    @Override
    public void visit(IntSort intSort)
    {
    }

    @Override
    public void visit(QuantifiedExpression quantifiedExpression)
    {
        for (VariableDeclaration boundVariable: quantifiedExpression.getVariables())
        {
            this.visit(boundVariable);
        }
        this.visit(quantifiedExpression.getExpression());
    }

    @Override
    public void visit(RealSort realSort)
    {

    }

    @Override
    public void visit(SetSort setSort)
    {
        visit(setSort.elementSort);
    }

    @Override
    public void visit(StringSort stringSort)
    {
    }

    @Override
    public void visit(TupleSort tupleSort)
    {
        for (Sort sort: tupleSort.elementSorts)
        {
            visit(sort);
        }
    }

    @Override
    public void visit(UnaryExpression unaryExpression)
    {
        visit(unaryExpression.getExpression());
    }

    @Override
    public void visit(UninterpretedSort uninterpretedSort)
    {
    }

    @Override
    public void visit(IntConstant intConstant)
    {
    }

    @Override
    public void visit(Variable variable)
    {
    }

    @Override
    public void visit(FunctionDeclaration functionDeclaration)
    {
        for (Sort sort: functionDeclaration.getInputSorts())
        {
            visit(sort);
        }
        visit(functionDeclaration.getSort());
    }

    @Override
    public void visit(FunctionDefinition functionDefinition)
    {
        for (VariableDeclaration variable: functionDefinition.getInputVariables())
        {
            visit(variable);
        }
        visit(functionDefinition.getExpression());
        visit(functionDefinition.getSort());
    }

    @Override
    public void visit(ConstantDeclaration constantDeclaration)
    {
        visit(constantDeclaration.getSort());
    }

    @Override
    public void visit(BoolConstant booleanConstant)
    {
    }

    @Override
    public void visit(Assertion assertion)
    {
        visit(assertion.getExpression());
    }

    @Override
    public void visit(MultiArityExpression expression)
    {
        for (Expression expr: expression.getExpressions())
        {
            visit(expr);
        }
    }

    @Override
    public void visit(FunctionCallExpression callExpression)
    {
        for (Expression expr: callExpression.getArguments())
        {
            visit(expr);
        }
    }

    @Override
    public void visit(VariableDeclaration variableDeclaration)
    {
        visit(variableDeclaration.getSort());
    }

    @Override
    public void visit(BoolSort boolSort)
    {
    }

    @Override
    public void visit(LetExpression letExpression)
    {
        for (Map.Entry<VariableDeclaration, Expression> entry : letExpression.getLetVariables().entrySet())
        {
            visit(entry.getKey());
            visit(entry.getValue());
        }
        visit(letExpression.getExpression());
    }

    @Override
    public void visit(ITEExpression iteExpression)
    {
        visit(iteExpression.getCondExpression());
        visit(iteExpression.getThenExpression());
        visit(iteExpression.getElseExpression());
    }

    @Override
    public void visit(UninterpretedConstant uninterpretedConstant)
    {
        visit(uninterpretedConstant.getSort());
    }

    @Override
    public void visit(SmtSettings smtSettings)
    {
    }

    @Override
    public void visit(SmtValues smtValues)
    {

    }

    @Override
    public void visit(ExpressionValue expressionValue)
    {

    }

    @Override
    public void visit(SmtUnsatCore smtUnsatCore)
    {

    }
}
