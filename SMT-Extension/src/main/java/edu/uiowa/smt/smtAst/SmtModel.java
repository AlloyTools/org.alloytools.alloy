/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.smt.smtAst;

import java.util.*;

public class SmtModel extends SmtAst
{
  protected final List<Sort> sorts = new ArrayList<>();
  protected List<FunctionDeclaration> functions = new ArrayList<>();

  public SmtModel()
  {
  }

  public SmtModel(SmtModel model)
  {
    this.sorts.addAll(model.sorts);
    this.functions.addAll(model.functions);
  }


  public void addSort(Sort sort)
  {
    if (sort != null)
    {
      this.sorts.add(sort);
    }
  }

  public void removeSort(Sort sort)
  {
    if (sort != null)
    {
      this.sorts.removeAll(Collections.singleton(sort));
    }
  }


  public void addFunction(FunctionDeclaration function)
  {
    if (function != null)
    {
      this.functions.add(function);
    }
  }

  public void addFunctions(List<FunctionDeclaration> functions)
  {
    for (FunctionDeclaration function : functions)
    {
      addFunction(function);
    }
  }

  public void removeFunction(FunctionDeclaration function)
  {
    if (function != null)
    {
      this.functions.removeAll(Collections.singleton(function));
    }
  }

  public void removeFunctions(List<FunctionDeclaration> functions)
  {
    this.functions.removeAll(functions);
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

  public FunctionDefinition evaluateUninterpretedInt(FunctionDefinition function)
  {
    Map<String, FunctionDefinition> functions = new HashMap<>();

    if (function.inputVariables.size() > 0)
    {
      throw new UnsupportedOperationException();
    }
    // make sure this is a cvc4 model
    for (FunctionDeclaration declaration : this.functions)
    {
      if (!(declaration instanceof FunctionDefinition))
      {
        throw new RuntimeException("The function " + declaration + " is not defined");
      }
      functions.put(declaration.getName(), (FunctionDefinition) declaration);
    }
    SmtExpr body = function.smtExpr.evaluate(functions);

    return new FunctionDefinition(function.getName(), function.inputVariables,
        function.getSort(), body, function.isOriginal());
  }

  protected void reset()
  {
    this.sorts.clear();
    this.functions.clear();
  }

  public void setFunctions(List<FunctionDeclaration> functions)
  {
    this.functions = functions;
  }
}
