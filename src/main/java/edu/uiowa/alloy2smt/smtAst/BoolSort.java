/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SMTAstVisitor;

/**
 *
 * @author Paul Meng
 */
public class BoolSort extends Sort {
    private final String boolSort = "Bool";
    
    public String getSortName()
    {
        return this.boolSort;
    }
    
    @Override
    public String toString() 
    {
        return this.boolSort;
    }

    @Override
    public void accept(SMTAstVisitor visitor) {
        visitor.visit(this);
    }    
}
