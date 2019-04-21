/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.printers;

import edu.uiowa.smt.smtAst.*;

import java.util.List;
import java.util.Map;

public class SmtLibPrettyPrinter implements SmtAstVisitor
{
    private StringBuilder stringBuilder = new StringBuilder();

    public String getSmtLib()
    {
        return stringBuilder.toString();
    }


    private void initializeProgram()
    {
        stringBuilder.append(
                "(set-logic ALL)\n" +
                "(set-option :produce-models true)\n" +
                "(set-option :incremental true)\n" +
                "(set-option :block-models true)\n" +
//                "(set-option :fmf-bound true)\n" +
                "(set-option :finite-model-find true)\n" +
                "(set-option :sets-ext true)\n");
    }

    public void visit(SmtProgram program)
    {
        initializeProgram();

        for(Sort sort : program.getSorts())
        {
            if(sort instanceof UninterpretedSort)
            {
                this.stringBuilder.append("(declare-sort ");
                this.stringBuilder.append(((UninterpretedSort) sort).getName());
                this.stringBuilder.append(" 0)\n");
            }
        }
        for (FunctionDeclaration declaration : program.getFunctions())
        {
            if(declaration instanceof  FunctionDefinition)
            {
                this.visit((FunctionDefinition) declaration);
            }
            else
            {
                this.visit(declaration);
            }
        }

        for (ConstantDeclaration declaration : program.getConstantDeclarations())
        {
            this.visit(declaration);
        }

        for (Assertion assertion: program.getAssertions())
        {
            this.visit(assertion);
        }
    }

    @Override
    public void visit(BinaryExpression binaryExpression)
    {
        if(binaryExpression.getOp() != BinaryExpression.Op.TUPSEL)
        {
            this.stringBuilder.append("(" + binaryExpression.getOp() + " ");
            this.visit(binaryExpression.getLhsExpr());
            this.stringBuilder.append(" ");
            this.visit(binaryExpression.getRhsExpr());
            this.stringBuilder.append(")");            
        }
        else
        {
            this.stringBuilder.append("((_ " + binaryExpression.getOp() + " ");
            this.stringBuilder.append(((IntConstant)binaryExpression.getLhsExpr()).getValue());
            this.stringBuilder.append(") ");
            this.visit(binaryExpression.getRhsExpr());
            this.stringBuilder.append(")");
        }
    }

    @Override
    public void visit(IntSort intSort)
    {
        this.stringBuilder.append(intSort.getName());
    }

    @Override
    public void visit(QuantifiedExpression quantifiedExpression)
    {
        this.stringBuilder.append("(" + quantifiedExpression.getOp() + " (");
        for (VariableDeclaration boundVariable: quantifiedExpression.getBoundVars())
        {
            this.visit(boundVariable);
        }
        this.stringBuilder.append(") ");
        this.visit(quantifiedExpression.getExpression());
        this.stringBuilder.append(")");
    }

    @Override
    public void visit(RealSort aThis)
    {
        throw new UnsupportedOperationException("Not supported yet.");
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
        for(int i = 0; i < tupleSort.elementSorts.size()-1; ++i)
        {
            this.visit(tupleSort.elementSorts.get(i));
            this.stringBuilder.append(" ");
        }
        this.visit(tupleSort.elementSorts.get(tupleSort.elementSorts.size()-1));
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
        this.stringBuilder.append(uninterpretedSort.getName());
    }

    @Override
    public void visit(IntConstant intConstant)
    {
        int value = Integer.parseInt(intConstant.getValue());
        if(value >= 0)
        {
            this.stringBuilder.append(intConstant.getValue());
        }
        else
        {
            this.stringBuilder.append("(- " + -value + ")");
        }
    }

    @Override
    public void visit(Variable variable)
    {
        this.stringBuilder.append(variable.getName());
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
        this.visit(functionDeclaration.getSort());
        this.stringBuilder.append(")\n");
    }

    @Override
    public void visit(FunctionDefinition funcDef)
    {
        this.stringBuilder.append("(define-fun ").append(funcDef.getName()).append(" (");
        for(VariableDeclaration bdVar : funcDef.inputVariables)
        {
            this.visit(bdVar);
        }
        this.stringBuilder.append(") ");
        this.visit(funcDef.getSort());
        this.stringBuilder.append(" ").append("\n");
        this.visit(funcDef.expression);
        this.stringBuilder.append(")");
        this.stringBuilder.append("\n");
    }

    @Override
    public void visit(ConstantDeclaration constantDeclaration)
    {
        this.stringBuilder.append("(declare-const ");
        this.stringBuilder.append(constantDeclaration.getName() + " ");
        this.visit(constantDeclaration.getSort());
        this.stringBuilder.append(")\n");
    }

    @Override
    public void visit(BoolConstant aThis) {
        this.stringBuilder.append(aThis.getValue());
    }

    @Override
    public void visit(Assertion assertion)
    {

        if(! assertion.getName().isEmpty())
        {
            // print comment
            this.stringBuilder.append("; " + assertion.getName() + "\n");
        }
        this.stringBuilder.append("(assert ");
        this.visit(assertion.getExpression());
        this.stringBuilder.append(")\n");
    }

    @Override
    public void visit(MultiArityExpression multiArityExpression)
    {
        this.stringBuilder.append("(" + multiArityExpression.getOp() + " ");
        if(multiArityExpression.getExpressions().size() == 1)
        {
            this.visit(multiArityExpression.getExpressions().get(0));
        }
        else if(multiArityExpression.getExpressions().size() > 1)
        {
            for (int i = 0; i < multiArityExpression.getExpressions().size()-1; ++i)
            {
                this.visit(multiArityExpression.getExpressions().get(i));
                this.stringBuilder.append(" ");
            }
            this.visit(multiArityExpression.getExpressions().get(multiArityExpression.getExpressions().size()-1));            
        }
        else
        {
            throw new RuntimeException("");
        }
        this.stringBuilder.append(")");
    }

    @Override
    public void visit(FunctionCallExpression functionCallExpression)
    {
        if(functionCallExpression.getArguments().size() > 0)
        {
            this.stringBuilder.append("(");
            this.stringBuilder.append(functionCallExpression.getFunctionName());            
            this.stringBuilder.append(" ");
            for(int i = 0; i < functionCallExpression.getArguments().size()-1; ++i)
            {
                this.visit(functionCallExpression.getArguments().get(i));
                this.stringBuilder.append(" ");
            }
            this.visit(functionCallExpression.getArguments().get(functionCallExpression.getArguments().size()-1));            
            this.stringBuilder.append(")");
        }
        else
        {
            this.stringBuilder.append(functionCallExpression.getFunctionName());
        }     
    }

    @Override
    public void visit(VariableDeclaration boundVariable)
    {
        this.stringBuilder.append("(" + boundVariable.getName() + " ");
        this.visit(boundVariable.getSort());
        this.stringBuilder.append(")");
    }

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
    public void visit(BoolSort aThis) {
        this.stringBuilder.append(aThis.getName());
    }

    @Override
    public void visit(LetExpression aThis) {
        this.stringBuilder.append("(" + aThis.getOp() + " (");
        for(Map.Entry<String, Expression> letVar : aThis.getLetVars().entrySet())
        {
            this.stringBuilder.append("(");
            this.stringBuilder.append(letVar.getKey()).append(" ");
            this.visit(letVar.getValue());
            this.stringBuilder.append(")");
        }
        this.stringBuilder.append(") ");
        this.visit(aThis.getExpression());
        this.stringBuilder.append(")");        
    }

    @Override
    public void visit(ITEExpression aThis) 
    {
        this.stringBuilder.append("(" + aThis.getOp() + " ");
        this.visit(aThis.getCondExpression());
        this.stringBuilder.append(" ");
        this.visit(aThis.getThenExpression());
        this.stringBuilder.append(" ");
        this.visit(aThis.getElseExpression());
        this.stringBuilder.append(")");
        
    }

    @Override
    public void visit(UninterpretedConstant uninterpretedConstant)
    {
        this.stringBuilder.append(uninterpretedConstant.getName());
    }

    @Override
    public void visit(SolverOption solverOption)
    {
        this.stringBuilder.append("(set-option ");
        this.stringBuilder.append(":" + solverOption.name + " ");
        this.stringBuilder.append(solverOption.value + ")\n");
    }
}
