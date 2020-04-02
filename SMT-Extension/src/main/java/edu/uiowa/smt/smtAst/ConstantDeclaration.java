/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

//ToDo: review whether the name VariableDeclaration is better
public class ConstantDeclaration extends Declaration
{
    public ConstantDeclaration(String name, Sort sort, boolean isOriginal)
    {
        super(name, sort, isOriginal);
    }

    @Override
    public void accept(SmtAstVisitor visitor) {
        visitor.visit(this);
    }
}
