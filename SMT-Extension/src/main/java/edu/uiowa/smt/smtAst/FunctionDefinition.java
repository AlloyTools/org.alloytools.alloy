/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import edu.uiowa.smt.printers.SmtLibPrinter;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class FunctionDefinition extends FunctionDeclaration
{
  public SmtExpr smtExpr;
  public final List<SmtVariable> inputVariables;

  public FunctionDefinition(String name, List<SmtVariable> inputVariables, Sort outputSort, SmtExpr smtExpr, boolean isOriginal)
  {
    super(name, inputVariables.stream().map(v -> v.getSort()).collect(Collectors.toList()), outputSort, isOriginal);
    this.inputVariables = inputVariables;
    this.smtExpr = smtExpr;
  }

  public FunctionDefinition(String name, SmtVariable inputVariable, Sort outputSort, SmtExpr smtExpr, boolean isOriginal)
  {
    super(name, inputVariable.getSort(), outputSort, isOriginal);
    this.inputVariables = Collections.singletonList(inputVariable);
    this.smtExpr = smtExpr;
  }

  public FunctionDefinition(String name, Sort outputSort, SmtExpr smtExpr, boolean isOriginal, SmtVariable... inputVariables)
  {
    super(name, Arrays.stream(inputVariables).map(v -> v.getSort()).collect(Collectors.toList()), outputSort, isOriginal);
    this.inputVariables = Arrays.asList(inputVariables);
    this.smtExpr = smtExpr;
  }

  public List<SmtVariable> getInputVariables()
  {
    return this.inputVariables;
  }

  public SmtExpr getBody()
  {
    return this.smtExpr;
  }

  @Override
  public void accept(SmtAstVisitor visitor)
  {
    visitor.visit(this);
  }

  @Override
  public String toString()
  {
    SmtLibPrinter printer = new SmtLibPrinter();
    printer.visit(this);
    return printer.getSmtLib();
  }

  public void setBody(SmtExpr smtExpr)
  {
    this.smtExpr = smtExpr;
  }
}