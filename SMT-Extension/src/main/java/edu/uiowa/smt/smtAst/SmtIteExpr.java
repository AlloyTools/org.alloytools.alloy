/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;

import java.util.List;
import java.util.Map;

/**
 * @author Mudathir Mohamed, Paul Meng
 */
public class SmtIteExpr extends SmtExpr
{
  private final SmtExpr condExpr;
  private final SmtExpr thenExpr;
  private final SmtExpr elseExpr;

  public SmtIteExpr(SmtExpr condExpr, SmtExpr thenExpr, SmtExpr elseExpr)
  {
    if (condExpr == null)
    {
      throw new RuntimeException("Condition expression of the ite is null");
    }
    if (thenExpr == null)
    {
      throw new RuntimeException("Then expression of the ite is null");
    }
    if (elseExpr == null)
    {
      throw new RuntimeException("Else expression of the ite is null");
    }
    this.condExpr = condExpr;
    this.thenExpr = thenExpr;
    this.elseExpr = elseExpr;
    checkTypes();
  }

  @Override
  protected void checkTypes()
  {
    if (condExpr.getSort() != AbstractTranslator.boolSort)
    {
      throw new RuntimeException(String.format("The sort '%1$s' of the condition expression is not boolean", condExpr.getSort()));
    }

    if (!thenExpr.getSort().equals(elseExpr.getSort()))
    {
      throw new RuntimeException(String.format("The sort '%1$s' of then expression is different than the sort '%1$s' of else expression", thenExpr.getSort(), elseExpr.getSort()));
    }
  }


  public SmtExpr getCondExpr()
  {
    return this.condExpr;
  }

  public SmtExpr getThenExpr()
  {
    return this.thenExpr;
  }

  public SmtExpr getElseExpr()
  {
    return this.elseExpr;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public Sort getSort()
  {
    return this.thenExpr.getSort();
  }

  @Override
  public SmtExpr evaluate(Map<String, FunctionDefinition> functions)
  {
    SmtExpr evaluatedCondition = condExpr.evaluate(functions);
    if (!(evaluatedCondition instanceof BoolConstant))
    {
      throw new RuntimeException("Expected a boolean constant but got " + evaluatedCondition);
    }
    boolean isTrue = Boolean.parseBoolean(((BoolConstant) evaluatedCondition).getValue());
    if (isTrue)
    {
      return thenExpr.evaluate(functions);
    }
    else
    {
      return elseExpr.evaluate(functions);
    }
  }

  @Override
  public boolean equals(Object object)
  {
    if (object == this)
    {
      return true;
    }
    if (!(object instanceof SmtIteExpr))
    {
      return false;
    }
    SmtIteExpr iteObject = (SmtIteExpr) object;
    return condExpr.equals(iteObject.condExpr) &&
        thenExpr.equals(iteObject.thenExpr) &&
        elseExpr.equals(iteObject.elseExpr);
  }

  @Override
  public List<Variable> getFreeVariables()
  {
    List<Variable> freeVariables = condExpr.getFreeVariables();
    freeVariables.addAll(thenExpr.getFreeVariables());
    freeVariables.addAll(elseExpr.getFreeVariables());
    return freeVariables;
  }

  @Override
  public SmtExpr substitute(Variable oldVariable, Variable newVariable)
  {
    if (condExpr.equals(newVariable) || thenExpr.equals(newVariable) || elseExpr.equals(newVariable))
    {
      throw new RuntimeException(String.format("Variable '%1$s' is not free in expression '%2$s'", newVariable, this));
    }
    SmtExpr newCondition = condExpr.substitute(oldVariable, newVariable);
    SmtExpr newThen = elseExpr.substitute(oldVariable, newVariable);
    SmtExpr newElse = elseExpr.substitute(oldVariable, newVariable);
    return new SmtIteExpr(newCondition, newThen, newElse);
  }

  @Override
  public SmtExpr replace(SmtExpr oldSmtExpr, SmtExpr newSmtExpr)
  {
    if (oldSmtExpr.equals(this))
    {
      return newSmtExpr;
    }
    SmtExpr newCondition = condExpr.replace(oldSmtExpr, newSmtExpr);
    SmtExpr newThen = elseExpr.replace(oldSmtExpr, newSmtExpr);
    SmtExpr newElse = elseExpr.replace(oldSmtExpr, newSmtExpr);
    return new SmtIteExpr(newCondition, newThen, newElse);
  }

  @Override
  public boolean containsExpr(SmtExpr expr)
  {
    if(expr.equals(this) ||
        this.condExpr.containsExpr(expr) ||
        this.thenExpr.containsExpr(expr) ||
        this.elseExpr.containsExpr(expr))
    {
      return true;
    }
    return false;
  }
}
