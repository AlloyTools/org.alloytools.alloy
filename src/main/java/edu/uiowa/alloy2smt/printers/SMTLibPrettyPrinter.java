/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.BinaryExpression;
import edu.uiowa.alloy2smt.smtAst.BooleanConstant;
import edu.uiowa.alloy2smt.smtAst.FunctionDeclaration;
import edu.uiowa.alloy2smt.smtAst.FunctionDefinition;
import edu.uiowa.alloy2smt.smtAst.IntConstant;
import edu.uiowa.alloy2smt.smtAst.IntSort;
import edu.uiowa.alloy2smt.smtAst.QuantifiedExpression;
import edu.uiowa.alloy2smt.smtAst.RealSort;
import edu.uiowa.alloy2smt.smtAst.SMTProgram;
import edu.uiowa.alloy2smt.smtAst.SetSort;
import edu.uiowa.alloy2smt.smtAst.StringSort;
import edu.uiowa.alloy2smt.smtAst.TupleSort;
import edu.uiowa.alloy2smt.smtAst.UnaryExpression;
import edu.uiowa.alloy2smt.smtAst.UninterpretedSort;
import edu.uiowa.alloy2smt.smtAst.VariableDeclaration;
import edu.uiowa.alloy2smt.smtAst.VariableExpression;

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
                "(declare-sort Atom 0)");
    }

    public String print()
    {
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
}
