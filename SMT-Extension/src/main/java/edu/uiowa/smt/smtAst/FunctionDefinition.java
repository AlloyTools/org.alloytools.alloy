/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class FunctionDefinition extends FunctionDeclaration
{
    public final SmtExpr smtExpr;
    public final List<VariableDeclaration>  inputVariables;
    
    public FunctionDefinition(String name, List<VariableDeclaration> inputVariables, Sort outputSort, SmtExpr smtExpr, boolean isOriginal)
    {
        super(name, inputVariables.stream().map(v -> v.getSort()).collect(Collectors.toList()), outputSort, isOriginal);
        this.inputVariables = inputVariables;
        this.smtExpr = smtExpr;
    }
    
    public FunctionDefinition(String name, VariableDeclaration inputVariable, Sort outputSort, SmtExpr smtExpr, boolean isOriginal)
    {
        super(name, inputVariable.getSort(), outputSort, isOriginal);
        this.inputVariables = Collections.singletonList(inputVariable);
        this.smtExpr = smtExpr;
    }
    public FunctionDefinition(String name, Sort outputSort, SmtExpr smtExpr, boolean isOriginal, VariableDeclaration... inputVariables)
    {
        super(name, Arrays.stream(inputVariables).map(v -> v.getSort()).collect(Collectors.toList()), outputSort, isOriginal);
        this.inputVariables = Arrays.asList(inputVariables);
        this.smtExpr = smtExpr;
    }      
    
    public List<VariableDeclaration> getInputVariables()
    {
        return this.inputVariables;
    }

    public SmtExpr getSmtExpr()
    {
        return this.smtExpr;
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
}