/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

//ToDo: review whether the name VariableDeclaration is better
public class ConstantDeclaration extends Declaration
{
    public ConstantDeclaration(String name, Sort sort)
    {
        super(name, sort);
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
