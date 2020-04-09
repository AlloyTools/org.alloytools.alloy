package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.*;
import edu.uiowa.smt.smtAst.SmtQtExpr;
import edu.uiowa.smt.smtAst.SmtExpr;

import java.util.*;

public class Environment
{
    private Map<String, SmtExpr> variablesMap = new HashMap<>();
    private Environment parent;
    //ToDo: review making this auxiliary formula more general
    private SmtQtExpr auxiliaryFormula = null;

    // top level environment
    public Environment()
    {
        parent = null;
        variablesMap = new HashMap<>();
    }
    public Environment(Environment parent)
    {
        this.parent = parent;
    }

    public void put(String key, SmtExpr value)
    {
        variablesMap.put(key, value);
    }

    public void putAll(Map<String, SmtExpr> map)
    {
        for(Map.Entry<String, SmtExpr> entry: map.entrySet())
        {
            put(entry.getKey(), entry.getValue());
        }
    }

    public SmtExpr get(String key)
    {
        Environment currentEnvironment = this;
        while(currentEnvironment != null)
        {
            SmtExpr value = currentEnvironment.variablesMap.get(key);
            if(value != null)
            {
                return value;
            }
            currentEnvironment = currentEnvironment.parent;
        }
        throw new RuntimeException(String.format("Can not find the variable %s in the environment", key));
    }

    public boolean containsKey(String key)
    {
        Environment currentEnvironment = this;
        while(currentEnvironment != null)
        {
            if(currentEnvironment.variablesMap.containsKey(key))
            {
                return true;
            }
            currentEnvironment = currentEnvironment.parent;
        }
        return false;
    }

    public Environment getParent()
    {
        return parent;
    }

    public LinkedHashMap<String, SmtExpr> getVariables()
    {
        return getVariablesAuxiliary(this);
    }

    private LinkedHashMap<String, SmtExpr> getVariablesAuxiliary(Environment environment)
    {
        if(environment.parent == null)
        {
            return new LinkedHashMap<>(environment.variablesMap);
        }

        LinkedHashMap<String, SmtExpr> map = getVariablesAuxiliary(environment.parent);
        map.putAll(environment.variablesMap);
        return map;
    }

    public void addAuxiliaryFormula(SmtQtExpr expression)
    {
        if(expression.getOp() != SmtQtExpr.Op.EXISTS)
        {
            throw new UnsupportedOperationException();
        }
        if(auxiliaryFormula == null)
        {
            auxiliaryFormula = expression;
        }
        else
        {
            List<VariableDeclaration> variables = new ArrayList<>(auxiliaryFormula.getVariables());
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
