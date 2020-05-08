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

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class SmtLibPrinter extends AbstractSmtAstVisitor
{
  public final static String CHECK_SAT = "(check-sat)";
  public final static String GET_MODEL = "(get-model)";
  public final static String GET_UNSAT_CORE = "(get-unsat-core)";
  public final static String BLOCK_MODEL = "(block-model)";
  public final static String PUSH = "(push 1)";
  public final static String POP = "(pop 1)";
  protected SmtSettings smtSettings;
  protected StringBuilder stringBuilder = new StringBuilder();

  public SmtLibPrinter(SmtSettings smtSettings)
  {
    this.smtSettings = smtSettings;
  }

  public SmtLibPrinter()
  {
    this.smtSettings = SmtSettings.Default;
  }


  public String getSmtLib()
  {
    return stringBuilder.toString();
  }


  protected void initializeProgram()
  {
    visit(smtSettings);
  }

  public void visit(SmtScript script)
  {
    if (script.getParent() == null)
    {
      initializeProgram();
    }

    for (Sort sort : script.getSorts())
    {
      if (sort instanceof UninterpretedSort)
      {
        stringBuilder.append("(declare-sort ");
        stringBuilder.append(sort.getName());
        stringBuilder.append(" 0)\n");
      }
    }
    for (FunctionDeclaration declaration : script.getFunctions())
    {
      if (declaration instanceof FunctionDefinition)
      {
        this.visit((FunctionDefinition) declaration);
      }
      else
      {
        this.visit(declaration);
      }
    }

    for (Assertion assertion : script.getAssertions())
    {
      this.visit(assertion);
    }
  }

  @Override
  public void visit(SmtBinaryExpr expr)
  {
    if (expr.getOp() != SmtBinaryExpr.Op.TUPSEL)
    {
      stringBuilder.append("(" + expr.getOp() + " ");
      this.visit(expr.getA());
      stringBuilder.append(" ");
      this.visit(expr.getB());
      stringBuilder.append(")");
    }
    else
    {
      stringBuilder.append("((_ " + expr.getOp() + " ");
      stringBuilder.append(((IntConstant) expr.getA()).getValue());
      stringBuilder.append(") ");
      this.visit(expr.getB());
      stringBuilder.append(")");
    }
  }

  @Override
  public void visit(IntSort intSort)
  {
    stringBuilder.append(intSort.getName());
  }

  @Override
  public void visit(SmtQtExpr smtQtExpr)
  {
    stringBuilder.append("(" + smtQtExpr.getOp() + " (");
    for (SmtVariable boundVariable : smtQtExpr.getVariables())
    {
      this.visit(boundVariable);
    }
    stringBuilder.append(") ");
    this.visit(smtQtExpr.getExpr());
    stringBuilder.append(")");
  }

  @Override
  public void visit(RealSort realSort)
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
  public void visit(StringSort stringSort)
  {
    throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
  }

  @Override
  public void visit(TupleSort tupleSort)
  {
    stringBuilder.append("(Tuple ");
    for (int i = 0; i < tupleSort.elementSorts.size() - 1; ++i)
    {
      this.visit(tupleSort.elementSorts.get(i));
      stringBuilder.append(" ");
    }
    this.visit(tupleSort.elementSorts.get(tupleSort.elementSorts.size() - 1));
    stringBuilder.append(")");
  }

  @Override
  public void visit(SmtUnaryExpr unaryExpression)
  {
    stringBuilder.append("(" + unaryExpression.getOp() + " ");
    this.visit(unaryExpression.getExpr());
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
    if (value >= 0)
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

    List<Sort> inputSorts = functionDeclaration.getInputSorts();
    for (int i = 0; i < inputSorts.size(); i++)
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
    for (SmtVariable bdVar : definition.inputVariables)
    {
      this.visit(bdVar);
    }
    stringBuilder.append(") ");
    this.visit(definition.getSort());
    stringBuilder.append(" ").append("\n");
    this.visit(definition.smtExpr);
    stringBuilder.append(")");
    stringBuilder.append("\n");
  }

  @Override
  public void visit(BoolConstant aThis)
  {
    stringBuilder.append(aThis.getValue());
  }

  @Override
  public void visit(Assertion assertion)
  {
    stringBuilder.append("\n");
    if (!assertion.getComment().isEmpty())
    {
      // print comment
      stringBuilder.append("; " + assertion.getComment() + "\n");
    }

    stringBuilder.append("(assert ");
    if (smtSettings.produceUnsatCore && !assertion.getSymbolicName().isEmpty())
    {
      stringBuilder.append("(! ");
    }
    this.visit(assertion.getSmtExpr());
    if (smtSettings.produceUnsatCore && !assertion.getSymbolicName().isEmpty())
    {
      stringBuilder.append("\n :named |" +
          assertion.getSymbolicName().replace("\\", "/")
          + "|))\n");
    }
    else
    {
      stringBuilder.append(")\n");
    }
  }

  @Override
  public void visit(SmtMultiArityExpr multiArityExpression)
  {
    stringBuilder.append("(" + multiArityExpression.getOp() + " ");
    if (multiArityExpression.getExprs().size() == 1)
    {
      this.visit(multiArityExpression.getExprs().get(0));
    }
    else if (multiArityExpression.getExprs().size() > 1)
    {
      for (int i = 0; i < multiArityExpression.getExprs().size() - 1; ++i)
      {
        this.visit(multiArityExpression.getExprs().get(i));
        stringBuilder.append(" ");
      }
      this.visit(multiArityExpression.getExprs().get(multiArityExpression.getExprs().size() - 1));
    }
    else
    {
      throw new RuntimeException("");
    }
    stringBuilder.append(")");
  }

  @Override
  public void visit(SmtCallExpr smtCallExpr)
  {
    if (smtCallExpr.getArguments().size() > 0)
    {
      stringBuilder.append("(");
      stringBuilder.append(TranslatorUtils.sanitizeWithBars(smtCallExpr.getFunction()));
      stringBuilder.append(" ");
      for (int i = 0; i < smtCallExpr.getArguments().size() - 1; ++i)
      {
        this.visit(smtCallExpr.getArguments().get(i));
        stringBuilder.append(" ");
      }
      this.visit(smtCallExpr.getArguments().get(smtCallExpr.getArguments().size() - 1));
      stringBuilder.append(")");
    }
    else
    {
      stringBuilder.append(TranslatorUtils.sanitizeWithBars(smtCallExpr.getFunction()));
    }
  }

  @Override
  public void visit(SmtVariable variable)
  {
    stringBuilder.append("(" + TranslatorUtils.sanitizeWithBars(variable) + " ");
    this.visit(variable.getSort());
    stringBuilder.append(")");
  }

  @Override
  public void visit(BoolSort aThis)
  {
    stringBuilder.append(aThis.getName());
  }

  @Override
  public void visit(SmtLetExpr let)
  {
    stringBuilder.append("(let (");
    for (Map.Entry<SmtVariable, SmtExpr> letVar : let.getLetVariables().entrySet())
    {
      stringBuilder.append("(");
      stringBuilder.append(TranslatorUtils.sanitizeWithBars(letVar.getKey())).append(" ");
      this.visit(letVar.getValue());
      stringBuilder.append(")");
    }
    stringBuilder.append(") ");
    this.visit(let.getSmtExpr());
    stringBuilder.append(")");
  }

  @Override
  public void visit(SmtIteExpr ite)
  {
    stringBuilder.append("(ite ");
    this.visit(ite.getCondExpr());
    stringBuilder.append(" ");
    this.visit(ite.getThenExpr());
    stringBuilder.append(" ");
    this.visit(ite.getElseExpr());
    stringBuilder.append(")");

  }

  @Override
  public void visit(UninterpretedConstant uninterpretedConstant)
  {
    stringBuilder.append(uninterpretedConstant.getName());
  }

  @Override
  public void visit(SmtSettings smtSettings)
  {
    for (String logic : smtSettings.getLogic())
    {
      stringBuilder.append("(set-logic " + logic + ")\n");
    }
    Map<String, String> options = smtSettings.getSolverOptions();
    for (Map.Entry<String, String> entry : options.entrySet())
    {
      stringBuilder.append("(set-option ");
      stringBuilder.append(":" + entry.getKey() + " ");
      stringBuilder.append(entry.getValue() + ")\n");
    }
  }

  public String printGetValue(SmtExpr smtExpr)
  {
    stringBuilder.append("(get-value (");
    visit(smtExpr);
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
    visit(expressionValue.getSmtExpr());
    stringBuilder.append(" ");
    visit(expressionValue.getValue());
    stringBuilder.append(")");
  }

  @Override
  public void visit(SmtUnsatCore smtUnsatCore)
  {
    stringBuilder.append("(\n");
    for (String formula : smtUnsatCore.getCore())
    {
      stringBuilder.append(formula + "\n");
    }
    stringBuilder.append(")");
  }
}
