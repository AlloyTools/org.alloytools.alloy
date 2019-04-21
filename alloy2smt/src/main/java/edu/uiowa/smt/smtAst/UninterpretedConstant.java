package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.Map;

public class UninterpretedConstant extends Constant
{

    private String name;
    private UninterpretedSort sort;

    public UninterpretedConstant(String name, UninterpretedSort sort)
    {
        this.name = name;
        this.sort = sort;
    }

    public String getName()
    {
        return name;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public Sort getSort()
    {
        return sort;
    }

    @Override
    public Expression evaluate(Map<String, FunctionDefinition> functions)
    {
        if(this.getSort().equals(AbstractTranslator.atomSort))
        {
            return this;
        }
        if(this.getSort().equals(AbstractTranslator.uninterpretedInt))
        {
            if(!functions.containsKey(AbstractTranslator.uninterpretedIntValueName))
            {
                throw new RuntimeException("The function " + AbstractTranslator.uninterpretedInt + " is undefined in this model");
            }
            // convert the uninterpreted int to int
            FunctionDefinition uninterpretedIntValue = functions.get(AbstractTranslator.uninterpretedIntValueName);
            // uninterpretedIntValue: UninterpretedInt -> Int
            assert (uninterpretedIntValue.inputVariables.size() == 1);
            FunctionCallExpression functionCall = new FunctionCallExpression(uninterpretedIntValue, this);
            return functionCall.evaluate(functions);
        }
        throw new UnsupportedOperationException();
    }
    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof UninterpretedConstant))
        {
            return false;
        }
        UninterpretedConstant constant = (UninterpretedConstant) object;
        return name.equals(constant.name) &&
                sort.equals(constant.sort);
    }
}
