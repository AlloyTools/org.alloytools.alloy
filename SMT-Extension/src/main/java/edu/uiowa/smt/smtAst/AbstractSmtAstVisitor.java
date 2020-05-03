package edu.uiowa.smt.smtAst;

import java.util.Map;

abstract public class AbstractSmtAstVisitor implements SmtAstVisitor
{
  @Override
  public void visit(SmtAst smtAst)
  {
    if (smtAst instanceof Assertion)
    {
      this.visit((Assertion) smtAst);
    }
    else if (smtAst instanceof Declaration)
    {
      this.visit((Declaration) smtAst);
    }
    else if (smtAst instanceof ExpressionValue)
    {
      this.visit((ExpressionValue) smtAst);
    }
    else if (smtAst instanceof SmtExpr)
    {
      this.visit((SmtExpr) smtAst);
    }
    else if (smtAst instanceof SmtScript)
    {
      this.visit((SmtScript) smtAst);
    }
    else if (smtAst instanceof SmtModel)
    {
      this.visit((SmtModel) smtAst);
    }
    else if (smtAst instanceof SmtSettings)
    {
      this.visit((SmtSettings) smtAst);
    }
    else if (smtAst instanceof SmtUnsatCore)
    {
      this.visit((SmtUnsatCore) smtAst);
    }
    else if (smtAst instanceof SmtValues)
    {
      this.visit((SmtValues) smtAst);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public void visit(Declaration declaration)
  {
    if (declaration instanceof FunctionDefinition)
    {
      this.visit((FunctionDefinition) declaration);
    }
    else if (declaration instanceof FunctionDeclaration)
    {
      this.visit((FunctionDeclaration) declaration);
    }
    else if (declaration instanceof SmtVariable)
    {
      this.visit((SmtVariable) declaration);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public void visit(SmtExpr smtExpr)
  {
    if (smtExpr instanceof Variable)
    {
      this.visit((Variable) smtExpr);
    }
    else if (smtExpr instanceof SmtUnaryExpr)
    {
      this.visit((SmtUnaryExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtBinaryExpr)
    {
      this.visit((SmtBinaryExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtMultiArityExpr)
    {
      this.visit((SmtMultiArityExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtQtExpr)
    {
      this.visit((SmtQtExpr) smtExpr);
    }
    else if (smtExpr instanceof Sort)
    {
      this.visit((Sort) smtExpr);
    }
    else if (smtExpr instanceof IntConstant)
    {
      this.visit((IntConstant) smtExpr);
    }
    else if (smtExpr instanceof SmtCallExpr)
    {
      this.visit((SmtCallExpr) smtExpr);
    }
    else if (smtExpr instanceof BoolConstant)
    {
      this.visit((BoolConstant) smtExpr);
    }
    else if (smtExpr instanceof SmtLetExpr)
    {
      this.visit((SmtLetExpr) smtExpr);
    }
    else if (smtExpr instanceof SmtIteExpr)
    {
      this.visit((SmtIteExpr) smtExpr);
    }
    else if (smtExpr instanceof UninterpretedConstant)
    {
      this.visit((UninterpretedConstant) smtExpr);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public void visit(Sort sort)
  {
    if (sort instanceof UninterpretedSort)
    {
      this.visit((UninterpretedSort) sort);
    }
    else if (sort instanceof SetSort)
    {
      this.visit((SetSort) sort);
    }
    else if (sort instanceof TupleSort)
    {
      this.visit((TupleSort) sort);
    }
    else if (sort instanceof IntSort)
    {
      this.visit((IntSort) sort);
    }
    else if (sort instanceof RealSort)
    {
      this.visit((RealSort) sort);
    }
    else if (sort instanceof StringSort)
    {
      this.visit((StringSort) sort);
    }
    else if (sort instanceof BoolSort)
    {
      this.visit((BoolSort) sort);
    }
    else
    {
      throw new UnsupportedOperationException();
    }
  }

  @Override
  public void visit(SmtModel model)
  {
  }

  @Override
  public void visit(SmtScript script)
  {
    for (Sort sort : script.getSorts())
    {
      visit(sort);
    }
    for (Declaration function : script.getFunctions())
    {
      visit(function);
    }
    for (Assertion assertion : script.getAssertions())
    {
      visit(assertion);
    }
  }

  @Override
  public void visit(SmtBinaryExpr expr)
  {
    visit(expr.getA());
    visit(expr.getB());
  }

  @Override
  public void visit(IntSort intSort)
  {
  }

  @Override
  public void visit(SmtQtExpr quantifiedExpression)
  {
    for (SmtVariable boundVariable : quantifiedExpression.getVariables())
    {
      this.visit(boundVariable);
    }
    this.visit(quantifiedExpression.getExpr());
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
    for (Sort sort : tupleSort.elementSorts)
    {
      visit(sort);
    }
  }

  @Override
  public void visit(SmtUnaryExpr unaryExpression)
  {
    visit(unaryExpression.getExpr());
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
    for (Sort sort : functionDeclaration.getInputSorts())
    {
      visit(sort);
    }
    visit(functionDeclaration.getSort());
  }

  @Override
  public void visit(FunctionDefinition functionDefinition)
  {
    for (SmtVariable variable : functionDefinition.getInputVariables())
    {
      visit(variable);
    }
    visit(functionDefinition.getBody());
    visit(functionDefinition.getSort());
  }

  @Override
  public void visit(BoolConstant booleanConstant)
  {
  }

  @Override
  public void visit(Assertion assertion)
  {
    visit(assertion.getSmtExpr());
  }

  @Override
  public void visit(SmtMultiArityExpr expression)
  {
    for (SmtExpr expr : expression.getExprs())
    {
      visit(expr);
    }
  }

  @Override
  public void visit(SmtCallExpr callExpression)
  {
    for (SmtExpr expr : callExpression.getArguments())
    {
      visit(expr);
    }
  }

  @Override
  public void visit(SmtVariable smtVariable)
  {
    visit(smtVariable.getSort());
  }

  @Override
  public void visit(BoolSort boolSort)
  {
  }

  @Override
  public void visit(SmtLetExpr letExpression)
  {
    for (Map.Entry<SmtVariable, SmtExpr> entry : letExpression.getLetVariables().entrySet())
    {
      visit(entry.getKey());
      visit(entry.getValue());
    }
    visit(letExpression.getSmtExpr());
  }

  @Override
  public void visit(SmtIteExpr iteExpression)
  {
    visit(iteExpression.getCondExpr());
    visit(iteExpression.getThenExpr());
    visit(iteExpression.getElseExpr());
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
