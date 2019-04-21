/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class FunctionDefinition extends FunctionDeclaration
{
    public final Expression                 expression;
    public final List<VariableDeclaration>  inputVariables;
    
    public FunctionDefinition(String name, List<VariableDeclaration> inputVariables, Sort outputSort, Expression expression)
    {
        super(name, inputVariables.stream().map(v -> v.getSort()).collect(Collectors.toList()), outputSort);
        this.inputVariables = inputVariables;
        this.expression = expression;
    }
    
    public FunctionDefinition(String name, VariableDeclaration inputVariable, Sort outputSort, Expression expression)
    {
        super(name, inputVariable.getSort(), outputSort);
        this.inputVariables = Collections.singletonList(inputVariable);
        this.expression = expression;
    }
    public FunctionDefinition(String name, Sort outputSort, Expression expression, VariableDeclaration... inputVariables)
    {
        super(name, Arrays.stream(inputVariables).map(v -> v.getSort()).collect(Collectors.toList()), outputSort);
        this.inputVariables = Arrays.asList(inputVariables);
        this.expression = expression;
    }      
    
    public List<VariableDeclaration> getInputVariables()
    {
        return this.inputVariables;
    }

    public Expression getExpression()
    {
        return this.expression;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
}