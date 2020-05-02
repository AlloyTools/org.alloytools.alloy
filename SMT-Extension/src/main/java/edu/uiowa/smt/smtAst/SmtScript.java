/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.printers.SmtLibPrettyPrinter;

import java.math.BigInteger;
import java.util.*;

public class SmtScript extends SmtModel
{
  private List<Assertion> assertions = new ArrayList<>();
  private SmtScript parent;
  //ToDo: refactor classes abstract translator and SmtScript
  private Map<BigInteger, FunctionDeclaration> integerConstants = new HashMap<>();
  // script between push pop commands
  private List<SmtScript> children = new ArrayList<>();

  public SmtScript()
  {
    parent = null;
  }

  public SmtScript(SmtScript smtScript)
  {
    super(smtScript);
    this.assertions.addAll(smtScript.assertions);
    this.parent = smtScript.parent;
    this.integerConstants.putAll(smtScript.integerConstants);
  }

  public Map<BigInteger, FunctionDeclaration> getIntegerConstants()
  {
    return integerConstants;
  }

  public void putIntegerConstant(BigInteger value, FunctionDeclaration declaration)
  {
    integerConstants.put(value, declaration);
    addFunction(declaration);
  }

  public SmtScript createChild()
  {
    SmtScript child = new SmtScript();
    child.parent = this;
    this.children.add(child);
    return child;
  }

  public void addAssertion(Assertion assertion)
  {
    if (assertion != null)
    {
      this.assertions.add(assertion);
    }
  }

  public void removeAssertion(Assertion assertion)
  {
    if (assertion != null)
    {
      this.assertions.removeAll(Collections.singleton(assertion));
    }
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
    this.assertions.clear();
    for (SmtScript child : children)
    {
      child.reset();
    }
  }

  public void removeAssertions(List<Assertion> assertions)
  {
    this.assertions.removeAll(assertions);
  }

  public SmtScript getParent()
  {
    return parent;
  }

  public SmtScript getChild(int index)
  {
    return children.get(index);
  }

  public void addAssertions(List<Assertion> assertions)
  {
    this.assertions.addAll(assertions);
  }

  public void addChild(SmtScript child)
  {
    child.parent = this;
    children.add(child);
  }

  public List<SmtScript> getChildren()
  {
    return children;
  }

  public boolean isUninterpretedIntUsed()
  {
    List<FunctionDeclaration> excludedFunctions = AbstractTranslator.getUninterpretedIntFunctions(this);
    for (FunctionDeclaration function : this.getFunctions())
    {
      if (excludedFunctions.contains(function))
      {
        // skip default functions for uninterpreted integers
        continue;
      }

      UninterpretedIntVisitor visitor = new UninterpretedIntVisitor();
      visitor.visit(function);
      if (visitor.isUninterpretedIntUsed())
      {
        return true;
      }

    }

    List<Assertion> excludedAssertions = AbstractTranslator.getUninterpretedIntAssertions(this);

    for (Assertion assertion : this.getAssertions())
    {
      if (excludedAssertions.contains(assertion))
      {
        // skip default assertions for uninterpreted integers
        continue;
      }

      UninterpretedIntVisitor visitor = new UninterpretedIntVisitor();
      visitor.visit(assertion);
      if (visitor.isUninterpretedIntUsed())
      {
        return true;
      }
    }

    // check children
    for (SmtScript child : this.getChildren())
    {
      if (child.isUninterpretedIntUsed())
      {
        return true;
      }
    }

    return false;
  }

  @Override
  public String toString()
  {
    SmtLibPrettyPrinter prettyPrinter = new SmtLibPrettyPrinter();
    prettyPrinter.visit(this);
    return prettyPrinter.getSmtLib();
  }

  public String print(SmtSettings settings)
  {
    SmtLibPrettyPrinter prettyPrinter = new SmtLibPrettyPrinter(settings);
    prettyPrinter.visit(this);
    return prettyPrinter.getSmtLib();
  }

  public void clearChildren()
  {
    this.children.clear();
  }
}
