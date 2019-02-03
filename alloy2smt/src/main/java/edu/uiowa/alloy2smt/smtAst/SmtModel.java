/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.smtAst;

import edu.uiowa.alloy2smt.printers.SmtAstVisitor;

import java.util.ArrayList;
import java.util.List;

public class SmtModel extends SmtAst
{
    protected final List<FunctionDeclaration>    functions = new ArrayList<>();
    protected final List<Sort>                   sorts     = new ArrayList<>();

    public SmtModel()
    {
    }

    public SmtModel(SmtModel model)
    {
        this.functions.addAll(model.functions);
        this.sorts.addAll(model.sorts);
    }


    public void addSort(Sort sort)
    {
        if(sort != null)
        {
            this.sorts.add(sort);
        }
    }



    public void addFunction(FunctionDeclaration function)
    {
        if(function != null)
        {
            this.functions.add(function);
        }
    }

    public List<Sort> getSorts()
    {
        return this.sorts;
    }

    public List<FunctionDeclaration> getFunctions()
    {
        return this.functions;
    }

    @Override
    public void accept(SmtAstVisitor visitor)
    {
        throw new UnsupportedOperationException();
    }
}
