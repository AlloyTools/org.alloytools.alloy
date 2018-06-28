/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

public class ConstantDeclaration extends SMTAst
{
    private final String                name;
    private final Sort                  sort;
    private final ConstantExpression    constantExpression;
    
    public ConstantDeclaration(String name, Sort sort)
    {
        this.name = name;
        this.sort = sort;
        constantExpression = new ConstantExpression(name);
    }
    
    public String getName()
    {
        return this.name;
    }
    
    public Sort getSort()
    {
        return this.sort;
    }

    public ConstantExpression getConstantExpr()
    {
        return this.constantExpression;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }
}
