package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.SmtExpr;
import edu.uiowa.smt.smtAst.SmtMultiArityExpr;
import edu.uiowa.smt.smtAst.SmtQtExpr;
import edu.uiowa.smt.smtAst.SmtVariable;

import java.util.*;

public class SmtEnv
{
  private Map<String, SmtExpr> variablesMap = new HashMap<>();
  private SmtEnv parent;
  //ToDo: review making this auxiliary formula more general
  private SmtQtExpr auxiliaryFormula = null;

  // top level environment
  public SmtEnv()
  {
    parent = null;
    variablesMap = new HashMap<>();
  }

  public SmtEnv(SmtEnv parent)
  {
    this.parent = parent;
  }

  public void put(String key, SmtExpr value)
  {
    variablesMap.put(key, value);
  }

  public void putAll(Map<String, SmtExpr> map)
  {
    for (Map.Entry<String, SmtExpr> entry : map.entrySet())
    {
      put(entry.getKey(), entry.getValue());
    }
  }

  public SmtExpr get(String key)
  {
    SmtEnv currentSmtEnv = this;
    while (currentSmtEnv != null)
    {
      SmtExpr value = currentSmtEnv.variablesMap.get(key);
      if (value != null)
      {
        return value;
      }
      currentSmtEnv = currentSmtEnv.parent;
    }
    throw new RuntimeException(String.format("Can not find the variable %s in the environment", key));
  }

  public boolean containsKey(String key)
  {
    SmtEnv currentSmtEnv = this;
    while (currentSmtEnv != null)
    {
      if (currentSmtEnv.variablesMap.containsKey(key))
      {
        return true;
      }
      currentSmtEnv = currentSmtEnv.parent;
    }
    return false;
  }

  public SmtEnv getParent()
  {
    return parent;
  }

  public LinkedHashMap<String, SmtExpr> getVariables()
  {
    return getVariablesAuxiliary(this);
  }

  private LinkedHashMap<String, SmtExpr> getVariablesAuxiliary(SmtEnv smtEnv)
  {
    if (smtEnv.parent == null)
    {
      return new LinkedHashMap<>(smtEnv.variablesMap);
    }

    LinkedHashMap<String, SmtExpr> map = getVariablesAuxiliary(smtEnv.parent);
    map.putAll(smtEnv.variablesMap);
    return map;
  }

  public void addAuxiliaryFormula(SmtQtExpr expression)
  {
    if (expression.getOp() != SmtQtExpr.Op.EXISTS)
    {
      throw new UnsupportedOperationException();
    }
    if (auxiliaryFormula == null)
    {
      auxiliaryFormula = expression;
    }
    else
    {
      List<SmtVariable> variables = new ArrayList<>(auxiliaryFormula.getVariables());
      variables.addAll(expression.getVariables());

      SmtExpr and = SmtMultiArityExpr.Op.AND.make(auxiliaryFormula.getExpression(), expression);
      auxiliaryFormula = SmtQtExpr.Op.EXISTS.make(and, variables);
    }
  }

  public SmtQtExpr getAuxiliaryFormula()
  {
    return auxiliaryFormula;
  }

  public void clearAuxiliaryFormula()
  {
    auxiliaryFormula = null;
  }
}
