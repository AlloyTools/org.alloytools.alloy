/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.printers;

import edu.uiowa.alloy2smt.smtAst.*;

import java.util.List;

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
        for (FunctionDeclaration declaration : this.program.getFunctionDeclarations())
        {
            this.visit(declaration);
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
        this.stringBuilder.append("(" + binaryExpression.getOp() + " ");
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
    public void visit(QuantifiedExpression quantifiedExpression)
    {
        this.stringBuilder.append("(" + quantifiedExpression.getOp() + " (");
        for (BoundVariableDeclaration boundVariable: quantifiedExpression.getBoundVars())
        {
            this.visit(boundVariable);
        }
        this.stringBuilder.append(") ");
        this.visit(quantifiedExpression.getExpression());
        this.stringBuilder.append(")");
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
    public void visit(UnaryExpression unaryExpression)
    {
        this.stringBuilder.append("(" + unaryExpression.getOP() + " ");
        this.visit(unaryExpression.getExpression());
        this.stringBuilder.append(")");
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
    public void visit(ConstantExpression constantExpression)
    {
        this.stringBuilder.append(constantExpression.getVarName());
    }

    @Override
    public void visit(FunctionDeclaration functionDeclaration)
    {
        this.stringBuilder.append("(declare-fun ");
        this.stringBuilder.append(functionDeclaration.getName() + " (");

        List<Sort> inputSorts  = functionDeclaration.getInputSorts();
        for(int i = 0 ; i < inputSorts.size(); i++)
        {
            this.visit(inputSorts.get(i));
        }
        this.stringBuilder.append(") ");
        this.visit(functionDeclaration.getOutputSort());
        this.stringBuilder.append(")\n");
    }

    @Override
    public void visit(FunctionDefinition aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(ConstantDeclaration constantDeclaration)
    {
        this.stringBuilder.append("(declare-const ");
        this.stringBuilder.append(constantDeclaration.getVarName() + " ");
        this.visit(constantDeclaration.getVarSort());
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

    @Override
    public void visit(MultiArityExpression multiArityExpression)
    {
        this.stringBuilder.append("(" + multiArityExpression.getOp() + " ");
        for (Expression expression: multiArityExpression.getExpressions())
        {
            this.visit(expression);
            this.stringBuilder.append(" ");
        }
        this.stringBuilder.append(")");
    }

    @Override
    public void visit(FunctionCallExpression functionCallExpression)
    {
        throw new UnsupportedOperationException();
    }

    @Override
    public void visit(BoundVariableDeclaration boundVariable)
    {
        this.stringBuilder.append("(" + boundVariable.getName() + " ");
        this.visit(boundVariable.getSort());
        this.stringBuilder.append(")");
    }

    private void visit(Expression expression)
    {
        if (expression instanceof ConstantExpression)
        {
            this.visit((ConstantExpression) expression);
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
