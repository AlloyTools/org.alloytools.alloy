/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;

import edu.mit.csail.sdg.parser.CompModule;
import edu.uiowa.alloy2smt.smtAst.SMTAst;

public class Alloy2SMTTranslator
{

    private CompModule alloyModel;

    public Alloy2SMTTranslator(CompModule alloyModel)
    {
        this.alloyModel = alloyModel;
    }

    public SMTAst execute()
    {
        throw new UnsupportedOperationException();
    }
}
