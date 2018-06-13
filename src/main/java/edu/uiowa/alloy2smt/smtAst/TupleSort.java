/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import java.util.Arrays;
import java.util.List;

public class TupleSort extends Sort
{
    public List<Sort> elementSorts;

    public TupleSort(List<Sort> elementSorts)
    {
        this.elementSorts = elementSorts;
    }

    public TupleSort(Sort ... elementSorts)
    {
        this.elementSorts = Arrays.asList(elementSorts);
    }
}
