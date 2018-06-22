/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.*;

public class SMTLibPrettyPrinter implements SMTAstVisitor
{
    private final SMTProgram program;

    private StringBuilder stringBuilder;

    public SMTLibPrettyPrinter(SMTProgram program)
    {
        this.program = program;
        initializeStringBuilder();
    }

    private void initializeStringBuilder()
    {
        stringBuilder = new StringBuilder();
        stringBuilder.append(
                "(set-logic ALL)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :finite-model-find true)\n" +
                "(declare-sort Atom 0)\n");
    }

    public String print()
    {
        for (VariableDeclaration variableDeclaration: this.program.getVariableDecls())
        {
            this.visit(variableDeclaration);
        }

        for (Assertion assertion: this.program.getAssertions())
        {
            this.visit(assertion);
        }

        throw new UnsupportedOperationException();
    }

    @Override
    public void visit(BinaryExpression bExpr) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(IntSort intSort) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(QuantifiedExpression aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(RealSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(SetSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(StringSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(TupleSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(UnaryExpression aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(UninterpretedSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(IntConstant aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(VariableExpression aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(FunctionDeclaration aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(FunctionDefinition aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(VariableDeclaration aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(BooleanConstant aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(Assertion assertion)
    {
        this.stringBuilder.append("(assert ");
        this.visit(assertion.getExpression());
        this.stringBuilder.append(")\n");
    }

    public void visit(Expression expression)
    {
        if (expression instanceof  UnaryExpression)
        {
            this.visit((UnaryExpression) expression);
        }
        else if (expression instanceof  BinaryExpression)
        {
            this.visit((BinaryExpression) expression);
        }
        else if (expression instanceof  QuantifiedExpression)
        {
            this.visit((QuantifiedExpression) expression);
        }
        else
        {
            throw new UnsupportedOperationException();
        }
    }
}
