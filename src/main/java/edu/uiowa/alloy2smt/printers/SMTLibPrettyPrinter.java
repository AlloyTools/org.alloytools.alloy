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

        return this.stringBuilder.toString();
    }

    @Override
    public void visit(BinaryExpression binaryExpression)
    {
        this.stringBuilder.append("(" + binaryExpression.getOp().toString() + " ");
        this.visit(binaryExpression.getLhsExpr());
        this.stringBuilder.append(" ");
        this.visit(binaryExpression.getRhsExpr());
        this.stringBuilder.append(")");
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
    public void visit(SetSort setSort)
    {
        this.stringBuilder.append("(Set ");
        this.visit(setSort.elementSort);
        this.stringBuilder.append(")");
    }

    @Override
    public void visit(StringSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(TupleSort tupleSort)
    {
        this.stringBuilder.append("(Tuple ");
        for (Sort sort: tupleSort.elementSorts)
        {
            this.visit(sort);
            this.stringBuilder.append(" ");
        }
        this.stringBuilder.append(")");
    }

    @Override
    public void visit(UnaryExpression aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(UninterpretedSort uninterpretedSort)
    {
        this.stringBuilder.append(uninterpretedSort.getSortName());
    }

    @Override
    public void visit(IntConstant aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(VariableExpression variableExpression)
    {
        this.stringBuilder.append(variableExpression.getVarName());
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
    public void visit(VariableDeclaration variableDeclaration)
    {
        this.stringBuilder.append("(declare-fun ");
        this.stringBuilder.append(variableDeclaration.getVarName() + " ");
        this.visit(variableDeclaration.getVarSort());
        this.stringBuilder.append(")\n");
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

    private void visit(Expression expression)
    {
        if (expression instanceof  VariableExpression)
        {
            this.visit((VariableExpression) expression);
        }
        else if (expression instanceof  UnaryExpression)
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

    private void visit(Sort sort)
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
        else
        {
            throw new UnsupportedOperationException();
        }
    }
}
