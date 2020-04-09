package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprLet;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.smtAst.SmtExpr;
import edu.uiowa.smt.smtAst.SmtLetExpr;
import edu.uiowa.smt.smtAst.SmtVariable;

import java.util.HashMap;
import java.util.Map;

public class ExprLetTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprLetTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    SmtExpr translateExprLet(ExprLet exprLet, Environment environment)
    {
        SmtExpr smtExpr = exprTranslator.translateExpr(exprLet.expr, environment);

        SmtVariable declaration = new SmtVariable(exprLet.var.label,
                smtExpr.getSort() , true);
        Map<SmtVariable, SmtExpr> map = new HashMap<>();
        map.put(declaration, smtExpr);

        Environment newEnvironment = new Environment(environment);
        newEnvironment.put(declaration.getName(), declaration.getVariable());
        SmtExpr body = exprTranslator.translateExpr(exprLet.sub, newEnvironment);
        SmtExpr let = new SmtLetExpr(map, body);
        return let;
    }
}
