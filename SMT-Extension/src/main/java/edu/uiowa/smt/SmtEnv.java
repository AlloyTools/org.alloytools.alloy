package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.SmtExpr;
import edu.uiowa.smt.smtAst.SmtVariable;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class SmtEnv
{
  private LinkedHashMap<String, SmtExpr> variablesMap = new LinkedHashMap<>();
  private List<SmtVariable> auxiliaryVariables = new ArrayList<>();
  private SmtEnv parent;

  // top level environment
  public SmtEnv()
  {
    parent = null;
    variablesMap = new LinkedHashMap<>();
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

  public List<SmtVariable> getAuxiliaryVariables()
  {
    return auxiliaryVariables;
  }

  public LinkedHashMap<String, SmtExpr> getVariables()
  {
    return getVariablesHelper(this);
  }

  private LinkedHashMap<String, SmtExpr> getVariablesHelper(SmtEnv smtEnv)
  {
    if (smtEnv.parent == null)
    {
      return new LinkedHashMap<>(smtEnv.variablesMap);
    }

    LinkedHashMap<String, SmtExpr> map = getVariablesHelper(smtEnv.parent);
    map.putAll(smtEnv.variablesMap);
    return map;
  }

  public void addAuxiliaryVariable(SmtVariable variable)
  {
    auxiliaryVariables.add(variable);
    variablesMap.put(variable.getName(), variable.getVariable());
  }
}
