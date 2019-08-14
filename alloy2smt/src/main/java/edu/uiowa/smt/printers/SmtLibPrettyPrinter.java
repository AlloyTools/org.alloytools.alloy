/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.printers;

import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.*;

public class SmtLibPrettyPrinter implements SmtAstVisitor
{
    public final static String CHECK_SAT = "(check-sat)";
    public final static String GET_MODEL = "(get-model)";
    public final static String GET_UNSAT_CORE = "(get-unsat-core)";
    public final static String BLOCK_MODEL = "(block-model)";
    public final static String PUSH = "(push 1)";
    public final static String POP = "(pop 1)";
    private Map<String, String> options;

    public SmtLibPrettyPrinter(Map<String, String> options)
    {
        this.options = options;
    }

    public SmtLibPrettyPrinter()
    {
        this.options = new HashMap<>();
    }

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
                "(set-option :block-models literals)\n" +
//                "(set-option :fmf-bound true)\n" +
                "(set-option :finite-model-find true)\n" +
                "(set-option :sets-ext true)\n");

        if(options != null && options.size() > 0)
        {
            for (Map.Entry<String, String> entry : options.entrySet())
            {
                SolverOption option = new SolverOption(entry.getKey(), entry.getValue());
                visit(option);
            }
        }
    }

    public void visit(SmtProgram program)
    {
        initializeProgram();

        for(Sort sort : program.getSorts())
        {
            if(sort instanceof UninterpretedSort)
            {
                stringBuilder.append("(declare-sort ");
                stringBuilder.append(sort.getName());
                stringBuilder.append(" 0)\n");
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
            stringBuilder.append("(" + binaryExpression.getOp() + " ");
            this.visit(binaryExpression.getLhsExpr());
            stringBuilder.append(" ");
            this.visit(binaryExpression.getRhsExpr());
            stringBuilder.append(")");            
        }
        else
        {
            stringBuilder.append("((_ " + binaryExpression.getOp() + " ");
            stringBuilder.append(((IntConstant)binaryExpression.getLhsExpr()).getValue());
            stringBuilder.append(") ");
            this.visit(binaryExpression.getRhsExpr());
            stringBuilder.append(")");
        }
    }

    @Override
    public void visit(IntSort intSort)
    {
        stringBuilder.append(intSort.getName());
    }

    @Override
    public void visit(QuantifiedExpression quantifiedExpression)
    {
        quantifiedExpression = optimize(quantifiedExpression);
        stringBuilder.append("(" + quantifiedExpression.getOp() + " (");
        for (VariableDeclaration boundVariable: quantifiedExpression.getVariables())
        {
            this.visit(boundVariable);
        }
        stringBuilder.append(") ");
        this.visit(quantifiedExpression.getExpression());
        stringBuilder.append(")");
    }

    public QuantifiedExpression optimize(QuantifiedExpression quantifiedExpression)
    {
        List<VariableDeclaration> declarations = new ArrayList<>();
        Map<VariableDeclaration, Expression> letVariables = new LinkedHashMap<>();
        for (VariableDeclaration variable: quantifiedExpression.getVariables())
        {
            if(variable.getSort() instanceof TupleSort)
            {
                List<Expression> tupleExpressions = new ArrayList<>();
                // convert tuple quantifiers to uninterpreted quantifiers
                TupleSort tupleSort = (TupleSort) variable.getSort();
                for (Sort sort: tupleSort.elementSorts)
                {
                    VariableDeclaration declaration = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
                    declarations.add(declaration);
                    tupleExpressions.add(declaration.getVariable());
                }
                Expression tuple = MultiArityExpression.Op.MKTUPLE.make(tupleExpressions);
                letVariables.put(variable, tuple);
            }
            else
            {
                declarations.add(variable);
            }
        }
        if(letVariables.size() > 0)
        {
            Expression let = new LetExpression(letVariables, quantifiedExpression.getExpression());
            return quantifiedExpression.getOp().make(let, declarations);
        }
        else
        {
            return  quantifiedExpression;
        }
    }

    @Override
    public void visit(RealSort aThis)
    {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public void visit(SetSort setSort)
    {
        stringBuilder.append("(Set ");
        this.visit(setSort.elementSort);
        stringBuilder.append(")");
    }

    @Override
    public void visit(StringSort aThis) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void visit(TupleSort tupleSort)
    {
        stringBuilder.append("(Tuple ");
        for(int i = 0; i < tupleSort.elementSorts.size()-1; ++i)
        {
            this.visit(tupleSort.elementSorts.get(i));
            stringBuilder.append(" ");
        }
        this.visit(tupleSort.elementSorts.get(tupleSort.elementSorts.size()-1));
        stringBuilder.append(")");
    }

    @Override
    public void visit(UnaryExpression unaryExpression)
    {
        stringBuilder.append("(" + unaryExpression.getOP() + " ");
        this.visit(unaryExpression.getExpression());
        stringBuilder.append(")");
    }

    @Override
    public void visit(UninterpretedSort uninterpretedSort)
    {
        stringBuilder.append(uninterpretedSort.getName());
    }

    @Override
    public void visit(IntConstant intConstant)
    {
        int value = Integer.parseInt(intConstant.getValue());
        if(value >= 0)
        {
            stringBuilder.append(intConstant.getValue());
        }
        else
        {
            stringBuilder.append("(- " + -value + ")");
        }
    }

    @Override
    public void visit(Variable variable)
    {
        stringBuilder.append(TranslatorUtils.sanitizeWithBars(variable.getDeclaration()));
    }

    @Override
    public void visit(FunctionDeclaration functionDeclaration)
    {
        stringBuilder.append("(declare-fun ");
        stringBuilder.append(TranslatorUtils.sanitizeWithBars(functionDeclaration) + " (");

        List<Sort> inputSorts  = functionDeclaration.getInputSorts();
        for(int i = 0 ; i < inputSorts.size(); i++)
        {
            this.visit(inputSorts.get(i));
        }
        stringBuilder.append(") ");
        this.visit(functionDeclaration.getSort());
        stringBuilder.append(")\n");
    }

    @Override
    public void visit(FunctionDefinition definition)
    {
        stringBuilder.append("(define-fun ").append(TranslatorUtils.sanitizeWithBars(definition)).append(" (");
        for(VariableDeclaration bdVar : definition.inputVariables)
        {
            this.visit(bdVar);
        }
        stringBuilder.append(") ");
        this.visit(definition.getSort());
        stringBuilder.append(" ").append("\n");
        this.visit(definition.expression);
        stringBuilder.append(")");
        stringBuilder.append("\n");
    }

    @Override
    public void visit(ConstantDeclaration constantDeclaration)
    {
        stringBuilder.append("(declare-const ");
        stringBuilder.append(TranslatorUtils.sanitizeWithBars(constantDeclaration) + " ");
        this.visit(constantDeclaration.getSort());
        stringBuilder.append(")\n");
    }

    @Override
    public void visit(BoolConstant aThis) {
        stringBuilder.append(aThis.getValue());
    }

    @Override
    public void visit(Assertion assertion)
    {
        if(! assertion.getComment().isEmpty())
        {
            // print comment
            stringBuilder.append("; " + assertion.getComment() + "\n");
        }

        stringBuilder.append("(assert ");
        if(! assertion.getSymbolicName().isEmpty())
        {
            stringBuilder.append("(! ");
        }
        this.visit(assertion.getExpression());
        if(assertion.getSymbolicName().isEmpty())
        {
            stringBuilder.append(")\n");
        }
        else
        {
            stringBuilder.append("\n :named |" +
                    assertion.getSymbolicName().replace("\\", "/")
                    + "|))\n");
        }
    }

    @Override
    public void visit(MultiArityExpression multiArityExpression)
    {
        stringBuilder.append("(" + multiArityExpression.getOp() + " ");
        if(multiArityExpression.getExpressions().size() == 1)
        {
            this.visit(multiArityExpression.getExpressions().get(0));
        }
        else if(multiArityExpression.getExpressions().size() > 1)
        {
            for (int i = 0; i < multiArityExpression.getExpressions().size()-1; ++i)
            {
                this.visit(multiArityExpression.getExpressions().get(i));
                stringBuilder.append(" ");
            }
            this.visit(multiArityExpression.getExpressions().get(multiArityExpression.getExpressions().size()-1));            
        }
        else
        {
            throw new RuntimeException("");
        }
        stringBuilder.append(")");
    }

    @Override
    public void visit(FunctionCallExpression functionCallExpression)
    {
        if(functionCallExpression.getArguments().size() > 0)
        {
            stringBuilder.append("(");
            stringBuilder.append(TranslatorUtils.sanitizeWithBars(functionCallExpression.getFunction()));
            stringBuilder.append(" ");
            for(int i = 0; i < functionCallExpression.getArguments().size()-1; ++i)
            {
                this.visit(functionCallExpression.getArguments().get(i));
                stringBuilder.append(" ");
            }
            this.visit(functionCallExpression.getArguments().get(functionCallExpression.getArguments().size()-1));            
            stringBuilder.append(")");
        }
        else
        {
            stringBuilder.append(TranslatorUtils.sanitizeWithBars(functionCallExpression.getFunction()));
        }     
    }

    @Override
    public void visit(VariableDeclaration variable)
    {
        stringBuilder.append("(" + TranslatorUtils.sanitizeWithBars(variable) + " ");
        this.visit(variable.getSort());
        stringBuilder.append(")");
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
        stringBuilder.append(aThis.getName());
    }

    @Override
    public void visit(LetExpression let) {
        stringBuilder.append("( let (");
        for(Map.Entry<VariableDeclaration, Expression> letVar : let.getLetVariables().entrySet())
        {
            stringBuilder.append("(");
            stringBuilder.append(TranslatorUtils.sanitizeWithBars(letVar.getKey())).append(" ");
            this.visit(letVar.getValue());
            stringBuilder.append(")");
        }
        stringBuilder.append(") ");
        this.visit(let.getExpression());
        stringBuilder.append(")");        
    }

    @Override
    public void visit(ITEExpression ite)
    {
        stringBuilder.append("(ite ");
        this.visit(ite.getCondExpression());
        stringBuilder.append(" ");
        this.visit(ite.getThenExpression());
        stringBuilder.append(" ");
        this.visit(ite.getElseExpression());
        stringBuilder.append(")");
        
    }

    @Override
    public void visit(UninterpretedConstant uninterpretedConstant)
    {
        stringBuilder.append(uninterpretedConstant.getName());
    }

    @Override
    public void visit(SolverOption solverOption)
    {
        stringBuilder.append("(set-option ");
        stringBuilder.append(":" + solverOption.name + " ");
        stringBuilder.append(solverOption.value + ")\n");
    }

    @Override
    public String printGetValue(Expression expression)
    {
        stringBuilder.append("(get-value (");
        visit(expression);
        stringBuilder.append("))");
        return stringBuilder.toString();
    }

    @Override
    public void visit(SmtValues smtValues)
    {
        stringBuilder.append("(");
        for (ExpressionValue value : smtValues.getValues())
        {
            visit(value);
        }
        stringBuilder.append(")");
    }

    @Override
    public void visit(ExpressionValue expressionValue)
    {
        stringBuilder.append("(");
        visit(expressionValue.getExpression());
        stringBuilder.append(" ");
        visit(expressionValue.getValue());
        stringBuilder.append(")");
    }

    @Override
    public void visit(SmtUnsatCore smtUnsatCore)
    {
        stringBuilder.append("(\n");
        for (String formula: smtUnsatCore.getCore())
        {
            stringBuilder.append(formula + "\n");
        }
        stringBuilder.append(")");
    }
}