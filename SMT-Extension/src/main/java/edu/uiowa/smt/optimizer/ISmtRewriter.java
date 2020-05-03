/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.optimizer;

import edu.uiowa.smt.smtAst.*;

public interface ISmtRewriter
{
  SmtRewriteResult visit(SmtAst smtAst);

  SmtRewriteResult visit(Declaration declaration);

  SmtRewriteResult visit(SmtModel model);

  SmtRewriteResult visit(SmtScript script);

  SmtRewriteResult visit(SmtBinaryExpr expr);

  SmtRewriteResult visit(Sort sort);

  SmtRewriteResult visit(IntSort intSort);

  SmtRewriteResult visit(SmtQtExpr quantifiedExpression);

  SmtRewriteResult visit(RealSort realSort);

  SmtRewriteResult visit(SetSort setSort);

  SmtRewriteResult visit(StringSort stringSort);

  SmtRewriteResult visit(TupleSort tupleSort);

  SmtRewriteResult visit(SmtExpr smtExpr);

  SmtRewriteResult visit(SmtUnaryExpr unaryExpression);

  SmtRewriteResult visit(UninterpretedSort uninterpretedSort);

  SmtRewriteResult visit(IntConstant intConstant);

  SmtRewriteResult visit(Variable variable);

  SmtRewriteResult visit(FunctionDeclaration functionDeclaration);

  SmtRewriteResult visit(FunctionDefinition functionDefinition);

  SmtRewriteResult visit(BoolConstant booleanConstant);

  SmtRewriteResult visit(Assertion assertion);

  SmtRewriteResult visit(SmtMultiArityExpr expression);

  SmtRewriteResult visit(SmtCallExpr smtCallExpr);

  SmtRewriteResult visit(SmtVariable smtVariable);

  SmtRewriteResult visit(BoolSort boolSort);

  SmtRewriteResult visit(SmtLetExpr letExpression);

  SmtRewriteResult visit(SmtIteExpr iteExpression);

  SmtRewriteResult visit(UninterpretedConstant uninterpretedConstant);

  SmtRewriteResult visit(SmtSettings smtSettings);

  SmtRewriteResult visit(SmtValues smtValues);

  SmtRewriteResult visit(ExpressionValue expressionValue);

  SmtRewriteResult visit(SmtUnsatCore smtUnsatCore);
}
