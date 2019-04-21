/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;
import edu.uiowa.smt.AbstractTranslator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SmtModel extends SmtAst
{
    protected final List<FunctionDeclaration>    functions = new ArrayList<>();
    protected final List<Sort>                   sorts     = new ArrayList<>();

    public SmtModel()
    {
    }

    public SmtModel(SmtModel model)
    {
        this.functions.addAll(model.functions);
        this.sorts.addAll(model.sorts);
    }


    public void addSort(Sort sort)
    {
        if(sort != null)
        {
            this.sorts.add(sort);
        }
    }



    public void addFunction(FunctionDeclaration function)
    {
        if(function != null)
        {
            this.functions.add(function);
        }
    }

    public List<Sort> getSorts()
    {
        return this.sorts;
    }

    public List<FunctionDeclaration> getFunctions()
    {
        return this.functions;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        throw new UnsupportedOperationException();
    }

    public FunctionDefinition evaluateUninterpretedInt(FunctionDefinition function)
    {
        Map<String, FunctionDefinition> functions = new HashMap<>();

        if(function.inputVariables.size() > 0)
        {
            throw new UnsupportedOperationException();
        }
        // make sure this is a cvc4 model
        for (FunctionDeclaration declaration: this.functions)
        {
            if(!(declaration instanceof FunctionDefinition))
            {
                throw new RuntimeException("The function " + declaration + " is not defined");
            }
            functions.put(declaration.getName(), (FunctionDefinition) declaration);
        }
        Expression body = function.expression.evaluate(functions);
        if(function.getSort().equals(AbstractTranslator.setOfUninterpretedIntTuple))
        {
            return new FunctionDefinition(function.getName(), function.inputVariables,
                    AbstractTranslator.setOfIntSortTuple, body);
        }
        if(function.getSort().equals(AbstractTranslator.setOfTernaryIntSort))
        {
            return new FunctionDefinition(function.getName(), function.inputVariables,
                    AbstractTranslator.setOfIntSortTuple, body);
        }
        throw new UnsupportedOperationException();
    }
}
