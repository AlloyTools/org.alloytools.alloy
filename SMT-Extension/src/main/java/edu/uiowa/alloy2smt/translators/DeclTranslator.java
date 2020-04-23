package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class DeclTranslator
{
  final ExprTranslator exprTranslator;
  final Alloy2SmtTranslator translator;

  public DeclTranslator(ExprTranslator exprTranslator)
  {
    this.exprTranslator = exprTranslator;
    this.translator = exprTranslator.translator;
  }

  public List<SmtVariable> translateDecls(List<Decl> decls, Environment environment)
  {
    List<SmtVariable> variables = new ArrayList<>();
    for (Decl decl: decls)
    {
      variables.addAll(translateDecl(decl, environment));
    }
    return variables;
  }

  public List<SmtVariable> translateDecl(Decl decl, Environment environment)
  {
    List<SmtVariable> variables = new ArrayList<>();

    for (ExprHasName name : decl.names)
    {
      Decl individualDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, Collections.singletonList(name), decl.expr);
      variables.add(translateIndividualDecl(individualDecl, environment));
    }

    //ToDo: disjoint

    //ToDo: disjoint2

    // add variables to the environment
    for (SmtVariable variable: variables)
    {
      environment.put(variable.getName(), variable.getVariable());
    }

    return variables;
  }

  public SmtVariable translateIndividualDecl(Decl decl, Environment environment)
  {
    ExprHasName name = decl.names.get(0);
    Expr expr = decl.expr;

    if (expr instanceof ExprUnary && ((ExprUnary) expr).op == ExprUnary.Op.NOOP)
    {
      expr = ((ExprUnary) expr).sub;
    }

    SmtExpr set = exprTranslator.translateExpr(expr, environment);
    SetSort setSort = (SetSort) set.getSort();
    Sort sort = setSort;

    // for singletons quantifiers has the same sort of the elements
    if (expr instanceof ExprUnary)
    {
      if (((ExprUnary) expr).op == ExprUnary.Op.ONEOF)
      {
        sort = setSort.elementSort;
        SmtVariable smtVariable = new SmtVariable(name.label, sort, true);
        assert (set instanceof SmtUnaryExpr);
        assert (((SmtUnaryExpr) set).getOP() == SmtUnaryExpr.Op.SINGLETON);
        assert (((SmtUnaryExpr) set).getExpression() instanceof Variable);
        Variable variable = (Variable) ((SmtUnaryExpr) set).getExpression();
        SmtExpr constraint = ((SmtVariable) variable.getDeclaration()).getConstraint();
        smtVariable.setConstraint(constraint.replace(variable, smtVariable.getVariable()));
        return smtVariable;
      }
    }

    SmtVariable smtVariable = new SmtVariable(name.label, sort, true);

    assert (set instanceof Variable);
    Variable variable = (Variable) set;
    if (variable.getDeclaration() instanceof SmtVariable)
    {
      SmtExpr constraint = ((SmtVariable) variable.getDeclaration()).getConstraint();
      if(constraint != null)
      {
        smtVariable.setConstraint(constraint.replace(variable, smtVariable.getVariable()));
      }
    }
    else
    {
      SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(smtVariable.getVariable(), variable);
      smtVariable.setConstraint(subset);
    }
    return smtVariable;
  }
}
