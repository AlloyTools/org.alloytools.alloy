package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class ExprCallTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprCallTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    SmtExpr translateExprCall(ExprCall exprCall, Environment environment)
    {
        String funcName = exprCall.fun.label;
        List<SmtExpr> argExprs = new ArrayList<>();

        for (Expr e : exprCall.args)
        {
            argExprs.add(exprTranslator.translateExpr(e, environment));
        }

//        if (this.translator.funcNamesMap.containsKey(funcName))
//        {
//            return new FunctionCallSmtExpr(translator.getFunctionFromAlloyName(funcName), argExprs);
//        }
//        else if (this.translator.setComprehensionFuncNameToInputsMap.containsKey(funcName))
//        {
//            return translateSetComprehensionFuncCallExpr(funcName, argExprs);
//        }
        if(exprCall.fun.pos.filename.contains("models/util/ordering.als".replace("/", File.separator)))
        {
            return new SmtCallExpr(translator.functionsMap.get(funcName), argExprs);
        }
//        else if (funcName.equals("integer/plus") || funcName.equals("integer/add"))
//        {
//            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinarySmtExpr.Op.PLUS, environment);
//        }
//        else if (funcName.equals("integer/minus") || funcName.equals("integer/sub"))
//        {
//            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinarySmtExpr.Op.MINUS, environment);
//        }
//        else if (funcName.equals("integer/mul"))
//        {
//            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinarySmtExpr.Op.MULTIPLY, environment);
//        }
//        else if (funcName.equals("integer/div"))
//        {
//            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinarySmtExpr.Op.DIVIDE, environment);
//        }
//        else if (funcName.equals("integer/rem"))
//        {
//            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinarySmtExpr.Op.MOD, environment);
//        }
//        else if (translator.functionsMap.containsKey(funcName))
//        {
//            FunctionDeclaration function = translator.getFunction(funcName);
//            return new FunctionCallSmtExpr(function, argExprs);
//        }
        else
        {
            Expr body = exprCall.fun.getBody();

            for (int i = 0; i < exprCall.args.size(); i++)
            {
                body = AlloyUtils.substituteExpr(body, exprCall.fun.get(i), exprCall.args.get(i));
            }
            SmtExpr callSmtExpr = exprTranslator.translateExpr(body, environment);
            return callSmtExpr;
        }
    }
}
