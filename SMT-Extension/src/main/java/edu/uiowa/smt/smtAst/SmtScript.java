/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SmtScript extends SmtModel
{
    private List<ConstantDeclaration>    constantDeclarations = new ArrayList<>();
    private List<Assertion>              assertions           = new ArrayList<>();

    public SmtScript()
    {
    }

    public SmtScript(SmtScript program)
    {
        super(program);
        this.constantDeclarations.addAll(program.constantDeclarations);
        this.assertions.addAll(program.assertions);
    }

    public void addConstantDeclaration(ConstantDeclaration constantDeclaration)
    {
        if(constantDeclaration != null)
        {
            this.constantDeclarations.add(constantDeclaration);
        }
    }

    public void addAssertion(Assertion assertion)
    {
        if(assertion != null)
        {
            this.assertions.add(assertion);
        }
    }

    public void removeAssertion(Assertion assertion)
    {
        if(assertion != null)
        {
            this.assertions.removeAll(Collections.singleton(assertion));
        }
    }

    public List<ConstantDeclaration> getConstantDeclarations()
    {
        return this.constantDeclarations;
    }

    public List<Assertion> getAssertions()
    {
        return this.assertions;
    }

    public void setAssertions(List<Assertion> assertions)
    {
        this.assertions = assertions;
    }

    public void reset()
    {
        super.reset();
        this.constantDeclarations.clear();
        this.assertions.clear();
    }

    public void removeAssertions(List<Assertion> assertions)
    {
        this.assertions.removeAll(assertions);
    }
}
