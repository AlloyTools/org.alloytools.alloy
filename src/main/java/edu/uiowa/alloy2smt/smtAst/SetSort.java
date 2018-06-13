/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

public class SetSort extends Sort
{
    public Sort elementSort;
    
    public SetSort(Sort elementSort) 
    {
        this.elementSort = elementSort;
    }
}
