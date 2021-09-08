package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.smt.SmtEnv;
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

  public List<SmtVariable> translateDecls(List<Decl> decls, SmtEnv smtEnv)
  {
    List<SmtVariable> variables = new ArrayList<>();
    for (Decl decl : decls)
    {
      variables.addAll(translateDecl(decl, smtEnv));
    }
    return variables;
  }

  public List<SmtVariable> translateDecl(Decl decl, SmtEnv smtEnv)
  {
    List<SmtVariable> variables = new ArrayList<>();

    for (ExprHasName name : decl.names)
    {
      Decl individualDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, decl.isVar, Collections.singletonList(name), decl.expr);
      variables.add(translateIndividualDecl(individualDecl, smtEnv));
    }

    // add variables to the environment
    for (SmtVariable variable : variables)
    {
      smtEnv.put(variable.getName(), variable.getVariable());
    }

    return variables;
  }

  public SmtVariable translateIndividualDecl(Decl decl, SmtEnv smtEnv)
  {
    ExprHasName name = decl.names.get(0);
    Expr expr = decl.expr;

    if (expr instanceof ExprUnary && ((ExprUnary) expr).op == ExprUnary.Op.NOOP)
    {
      expr = ((ExprUnary) expr).sub;
    }

    SmtEnv newEnv = new SmtEnv(smtEnv);
    SmtExpr set = exprTranslator.translateExpr(expr, newEnv);
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
        assert (((SmtUnaryExpr) set).getOp() == SmtUnaryExpr.Op.SINGLETON);
        assert (((SmtUnaryExpr) set).getExpr() instanceof Variable);
        Variable variable = (Variable) ((SmtUnaryExpr) set).getExpr();
        SmtExpr constraint = ((SmtVariable) variable.getDeclaration()).getConstraint();
        smtVariable.setConstraint(constraint.replace(variable, smtVariable.getVariable()));
        return smtVariable;
      }
    }

    SmtVariable smtVariable = new SmtVariable(name.label, sort, true);

    if (set instanceof Variable && ((Variable) set).getDeclaration() instanceof SmtVariable)
    {
      Variable variable = (Variable) set;
      SmtExpr constraint = ((SmtVariable) variable.getDeclaration()).getConstraint();
      if (constraint != null)
      {
        smtVariable.setConstraint(constraint.replace(variable, smtVariable.getVariable()));
      }
    }
    else
    {
      SmtExpr subset = SmtBinaryExpr.Op.SUBSET.make(smtVariable.getVariable(), set);
      smtVariable.setConstraint(subset);
    }
    return smtVariable;
  }

  public SmtExpr getDisjointConstraints(List<Decl> decls, SmtEnv smtEnv)
  {
    SmtExpr disjointConstraints = BoolConstant.True;

    for (Decl decl : decls)
    {
      // disjoint fields
      if (decl.disjoint != null && decl.names.size() > 1)
      {
        for (int i = 0; i < decl.names.size() - 1; i++)
        {
          for (int j = i + 1; j < decl.names.size(); j++)
          {
            SmtExpr variableI = smtEnv.get(decl.names.get(i).label);
            SmtExpr variableJ = smtEnv.get(decl.names.get(j).label);

            if (variableJ.getSort() instanceof UninterpretedSort)
            {
              throw new UnsupportedOperationException();
            }

            if (variableJ.getSort() instanceof TupleSort)
            {
              variableI = SmtUnaryExpr.Op.SINGLETON.make(variableI);
              variableJ = SmtUnaryExpr.Op.SINGLETON.make(variableJ);
            }

            SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(variableI, variableJ);
            SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(variableI.getSort());
            SmtExpr equal = SmtBinaryExpr.Op.EQ.make(intersect, emptySet);
            disjointConstraints = SmtMultiArityExpr.Op.AND.make(disjointConstraints, equal);
          }
        }
      }
    }
    return disjointConstraints;
  }
}
