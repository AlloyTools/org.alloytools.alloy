/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.*;

public interface SmtAstVisitor
{
    public void visit(SmtProgram program);

    public void visit(BinaryExpression bExpr);

    public void visit(Sort intSort);
    
    public void visit(IntSort intSort);   

    public void visit(QuantifiedExpression quantifiedExpression);

    public void visit(RealSort realSort);

    public void visit(SetSort setSort);

    public void visit(StringSort stringSort);

    public void visit(TupleSort tupleSort);

    public void visit(Expression expression);

    public void visit(UnaryExpression unaryExpression);

    public void visit(UninterpretedSort uninterpretedSort);

    public void visit(IntConstant intConstant);

    public void visit(ConstantExpression constantExpression);

    public void visit(FunctionDeclaration functionDeclaration);

    public void visit(FunctionDefinition functionDefinition);

    public void visit(ConstantDeclaration constantDeclaration);

    public void visit(BooleanConstant booleanConstant);

    public void visit(Assertion assertion);

    public void visit(MultiArityExpression expression);

    public void visit(FunctionCallExpression functionCallExpression);

    public void visit(VariableDeclaration variableDeclaration);

    public void visit(BoolSort boolSort);

    public void visit(LetExpression letExpression);

    public void visit(ITEExpression iteExpression);

    public void visit(AtomConstant atomConstant);

    public void visit(SolverOption solverOption);
}
