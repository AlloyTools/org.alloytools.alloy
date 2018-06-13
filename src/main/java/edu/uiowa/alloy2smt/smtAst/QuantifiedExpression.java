/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class QuantifiedExpression extends Expression
{
    public enum Op 
    {        
        FORALL ("forall"),
        EXISTS ("exists");    

        private final String opStr;

        private Op(String op) 
        {
            this.opStr = op;
        }

        @Override
        public String toString() 
        {
            return this.opStr;
        }        
    }    
}
