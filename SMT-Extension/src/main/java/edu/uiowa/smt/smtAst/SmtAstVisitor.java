/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

public interface SmtAstVisitor
{
  void visit(SmtAst smtAst);

  void visit(Declaration declaration);

  void visit(SmtModel model);

  void visit(SmtScript script);

  void visit(SmtBinaryExpr expr);

  void visit(Sort sort);

  void visit(IntSort intSort);

  void visit(SmtQtExpr quantifiedExpression);

  void visit(RealSort realSort);

  void visit(SetSort setSort);

  void visit(StringSort stringSort);

  void visit(TupleSort tupleSort);

  void visit(SmtExpr smtExpr);

  void visit(SmtUnaryExpr unaryExpression);

  void visit(UninterpretedSort uninterpretedSort);

  void visit(IntConstant intConstant);

  void visit(Variable variable);

  void visit(FunctionDeclaration functionDeclaration);

  void visit(FunctionDefinition functionDefinition);

  void visit(BoolConstant booleanConstant);

  void visit(Assertion assertion);

  void visit(SmtMultiArityExpr expression);

  void visit(SmtCallExpr smtCallExpr);

  void visit(SmtVariable smtVariable);

  void visit(BoolSort boolSort);

  void visit(SmtLetExpr letExpression);

  void visit(SmtIteExpr iteExpression);

  void visit(UninterpretedConstant uninterpretedConstant);

  void visit(SmtSettings smtSettings);

  void visit(SmtValues smtValues);

  void visit(ExpressionValue expressionValue);

  void visit(SmtUnsatCore smtUnsatCore);
}
