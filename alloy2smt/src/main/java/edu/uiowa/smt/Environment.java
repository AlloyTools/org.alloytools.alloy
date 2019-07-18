package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.Expression;
import edu.uiowa.smt.smtAst.MultiArityExpression;
import edu.uiowa.smt.smtAst.QuantifiedExpression;
import edu.uiowa.smt.smtAst.VariableDeclaration;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class Environment
{
    private Map<String, Expression> variablesMap = new HashMap<>();
    private Environment parent;
    //ToDo: review making this auxiliary formula more general
    private QuantifiedExpression auxiliaryFormula = null;

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
    public void put(String key, Expression value)
    {
        variablesMap.put(key, value);
    }

    public Expression get(String key)
    {
        Environment currentEnvironment = this;
        while(currentEnvironment != null)
        {
            Expression value = currentEnvironment.variablesMap.get(key);
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

    public LinkedHashMap<String, Expression> getVariables()
    {
        return getVariablesAuxiliary(this);
    }

    private LinkedHashMap<String, Expression> getVariablesAuxiliary(Environment environment)
    {
        if(environment.parent == null)
        {
            return new LinkedHashMap<>(environment.variablesMap);
        }

        LinkedHashMap<String, Expression> map = getVariablesAuxiliary(environment.parent);
        map.putAll(environment.variablesMap);
        return map;
    }

    public void addAuxiliaryFormula(QuantifiedExpression expression)
    {
        if(expression.getOp() != QuantifiedExpression.Op.EXISTS)
        {
            throw new UnsupportedOperationException();
        }
        if(auxiliaryFormula == null)
        {
            auxiliaryFormula = expression;
        }
        else
        {
            List<VariableDeclaration> variables = auxiliaryFormula.getVariables();
            variables.addAll(expression.getVariables());

            Expression and = MultiArityExpression.Op.AND.make(auxiliaryFormula.getExpression(), expression);
            auxiliaryFormula = QuantifiedExpression.Op.EXISTS.make(and, variables);
        }
    }

    public QuantifiedExpression getAuxiliaryFormula()
    {
        return auxiliaryFormula;
    }
}
