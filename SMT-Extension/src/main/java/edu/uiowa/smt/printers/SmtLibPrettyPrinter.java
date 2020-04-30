package edu.uiowa.smt.printers;

import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.Map;

public class SmtLibPrettyPrinter extends SmtLibPrinter
{
  private int tabsCount = 0;

  private void printTabs()
  {
    for (int i = 0; i < tabsCount; i++)
    {
      stringBuilder.append(" ");
    }
  }

  public SmtLibPrettyPrinter(SmtSettings smtSettings)
  {
    super(smtSettings);
  }

  public SmtLibPrettyPrinter()
  {
    super();
  }

  @Override
  public void visit(SmtUnaryExpr unaryExpression)
  {
    tabsCount++;
    stringBuilder.append("\n");
    printTabs();
    stringBuilder.append("(" + unaryExpression.getOP() + " ");
    tabsCount++;
    this.visit(unaryExpression.getExpression());
    stringBuilder.append(")");
    tabsCount -= 2;

  }

  @Override
  public void visit(SmtBinaryExpr expr)
  {
    if (expr.getOp() != SmtBinaryExpr.Op.TUPSEL)
    {
      tabsCount++;
      stringBuilder.append("\n");
      printTabs();
      stringBuilder.append("(" + expr.getOp() + " ");
      tabsCount++;
      this.visit(expr.getA());
      stringBuilder.append(" ");
      this.visit(expr.getB());
      stringBuilder.append(")");
      tabsCount -= 2;
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
  public void visit(SmtMultiArityExpr multiArityExpression)
  {
    tabsCount++;
    stringBuilder.append("\n");
    printTabs();
    stringBuilder.append("(" + multiArityExpression.getOp() + " ");
    tabsCount++;
    if (multiArityExpression.getExpressions().size() == 1)
    {
      this.visit(multiArityExpression.getExpressions().get(0));
    }
    else if (multiArityExpression.getExpressions().size() > 1)
    {
      for (int i = 0; i < multiArityExpression.getExpressions().size() - 1; ++i)
      {
        this.visit(multiArityExpression.getExpressions().get(i));
        stringBuilder.append(" ");
      }
      this.visit(multiArityExpression.getExpressions().get(multiArityExpression.getExpressions().size() - 1));
    }
    else
    {
      throw new RuntimeException("");
    }
    stringBuilder.append(")");
    tabsCount -= 2;
  }

  @Override
  public void visit(SmtQtExpr quantifiedExpression)
  {
    quantifiedExpression = optimize(quantifiedExpression);
    tabsCount++;
    stringBuilder.append("\n");
    printTabs();
    stringBuilder.append("(" + quantifiedExpression.getOp() + " (");
    for (SmtVariable boundVariable : quantifiedExpression.getVariables())
    {
      this.visit(boundVariable);
    }
    stringBuilder.append(") ");
    tabsCount++;
    this.visit(quantifiedExpression.getExpression());
    stringBuilder.append(")");
    tabsCount -= 2;
  }

  @Override
  public void visit(SmtLetExpr let)
  {
    tabsCount++;
    stringBuilder.append("\n");
    printTabs();
    stringBuilder.append("(let (");
    for (Map.Entry<SmtVariable, SmtExpr> letVar : let.getLetVariables().entrySet())
    {
      tabsCount++;
      stringBuilder.append("\n");
      printTabs();
      stringBuilder.append("(");
      stringBuilder.append(TranslatorUtils.sanitizeWithBars(letVar.getKey())).append(" ");
      this.visit(letVar.getValue());
      stringBuilder.append(")");
      tabsCount--;
    }
    stringBuilder.append(") ");
    tabsCount++;
    this.visit(let.getSmtExpr());
    stringBuilder.append(")");
    tabsCount -= 2;
  }

  @Override
  public void visit(SmtExpr smtExpr)
  {
    super.visit(smtExpr);
    if (!smtExpr.getComment().isEmpty())
    {
      stringBuilder.append("; " + smtExpr.getComment() + "\n");
      printTabs();
    }
  }
}
