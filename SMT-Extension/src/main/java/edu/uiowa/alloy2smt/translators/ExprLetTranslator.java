package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.smtAst.Expression;

public class ExprLetTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprLetTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    Expression translateExprLet(ExprLet exprLet, Environment environment)
    {
        Expr letExpanded = AlloyUtils.substituteExpr(exprLet.sub, exprLet.var, exprLet.expr);
        Expression letTranslation = exprTranslator.translateExpr(letExpanded, environment);
        return letTranslation;
    }
}
