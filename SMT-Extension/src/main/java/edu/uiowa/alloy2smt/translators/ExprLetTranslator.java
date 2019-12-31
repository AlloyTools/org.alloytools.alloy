package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.Expression;
import edu.uiowa.smt.smtAst.FunctionDeclaration;
import edu.uiowa.smt.smtAst.LetExpression;
import edu.uiowa.smt.smtAst.VariableDeclaration;

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

    Expression translateExprLet(ExprLet exprLet, Environment environment)
    {
        Expression expression = exprTranslator.translateExpr(exprLet.expr, environment);

        VariableDeclaration declaration = new VariableDeclaration(exprLet.var.label,
                expression.getSort() , true);
        Map<VariableDeclaration, Expression> map = new HashMap<>();
        map.put(declaration, expression);

        Environment newEnvironment = new Environment(environment);
        newEnvironment.put(declaration.getName(), declaration.getVariable());
        Expression body = exprTranslator.translateExpr(exprLet.sub, newEnvironment);
        Expression let = new LetExpression(map, body);
        return let;
    }
}
