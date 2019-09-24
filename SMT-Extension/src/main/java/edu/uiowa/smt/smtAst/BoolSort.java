/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtAstVisitor;

/**
 *
 * @author Paul Meng, Mudathir Mahgoub
 */
public class BoolSort extends Sort
{

    private static BoolSort instance = new BoolSort();

    private BoolSort()
    {
        super("Bool", 0);
    }

    public static BoolSort getInstance()
    {
        return instance;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        visitor.visit(this);
    }

    @Override
    public boolean equals(Object object)
    {
        if(object == this)
        {
            return true;
        }
        if(!(object instanceof BoolSort))
        {
            return false;
        }
        return true;
    }
}
