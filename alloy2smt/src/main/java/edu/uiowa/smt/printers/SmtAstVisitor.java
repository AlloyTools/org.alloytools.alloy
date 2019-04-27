/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.printers;

import edu.uiowa.smt.smtAst.*;

public interface SmtAstVisitor
{
    void visit(SmtProgram program);

    void visit(BinaryExpression bExpr);

    void visit(Sort intSort);
    
    void visit(IntSort intSort);

    void visit(QuantifiedExpression quantifiedExpression);

    void visit(RealSort realSort);

    void visit(SetSort setSort);

    void visit(StringSort stringSort);

    void visit(TupleSort tupleSort);

    void visit(Expression expression);

    void visit(UnaryExpression unaryExpression);

    void visit(UninterpretedSort uninterpretedSort);

    void visit(IntConstant intConstant);

    void visit(Variable variable);

    void visit(FunctionDeclaration functionDeclaration);

    void visit(FunctionDefinition functionDefinition);

    void visit(ConstantDeclaration constantDeclaration);

    void visit(BoolConstant booleanConstant);

    void visit(Assertion assertion);

    void visit(MultiArityExpression expression);

    void visit(FunctionCallExpression functionCallExpression);

    void visit(VariableDeclaration variableDeclaration);

    void visit(BoolSort boolSort);

    void visit(LetExpression letExpression);

    void visit(ITEExpression iteExpression);

    void visit(UninterpretedConstant uninterpretedConstant);

    void visit(SolverOption solverOption);

    String printGetValue(Expression expression);

    void visit(SmtValues smtValues);

    void visit(ExpressionValue expressionValue);
}
