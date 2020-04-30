package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.Func;
import edu.uiowa.smt.SmtEnv;
import edu.uiowa.smt.smtAst.*;

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

  SmtExpr translateExprCall(ExprCall exprCall, SmtEnv smtEnv)
  {
    String funcName = exprCall.fun.label;
//
////    if (exprCall.fun.pos.filename.contains("models/util/ordering.als".replace("/", File.separator)))
////    {
////      return new SmtCallExpr(translator.functionsMap.get(func.label), arguments);
////    }
    if (funcName.equals("integer/plus") || funcName.equals("integer/add"))
    {
      Expr expr = ExprBinary.Op.IPLUS.make(null, null, exprCall.args.get(0), exprCall.args.get(1));
      return exprTranslator.exprBinaryTranslator.translateArithmetic((ExprBinary) expr, SmtBinaryExpr.Op.PLUS, smtEnv);
    }
    else if (funcName.equals("integer/minus") || funcName.equals("integer/sub"))
    {
      Expr expr = ExprBinary.Op.IMINUS.make(null, null, exprCall.args.get(0), exprCall.args.get(1));
      return exprTranslator.exprBinaryTranslator.translateArithmetic((ExprBinary) expr, SmtBinaryExpr.Op.MINUS, smtEnv);
    }
    else if (funcName.equals("integer/mul"))
    {
      Expr expr = ExprBinary.Op.MUL.make(null, null, exprCall.args.get(0), exprCall.args.get(1));
      return exprTranslator.exprBinaryTranslator.translateArithmetic((ExprBinary) expr, SmtBinaryExpr.Op.MULTIPLY, smtEnv);
    }
    else if (funcName.equals("integer/div"))
    {
      Expr expr = ExprBinary.Op.DIV.make(null, null, exprCall.args.get(0), exprCall.args.get(1));
      return exprTranslator.exprBinaryTranslator.translateArithmetic((ExprBinary) expr, SmtBinaryExpr.Op.DIVIDE, smtEnv);
    }
    else if (funcName.equals("integer/rem"))
    {
      Expr expr = ExprBinary.Op.REM.make(null, null, exprCall.args.get(0), exprCall.args.get(1));
      return exprTranslator.exprBinaryTranslator.translateArithmetic((ExprBinary) expr, SmtBinaryExpr.Op.MOD, smtEnv);
    }

    return buildSmtCallExpr(exprCall, smtEnv);
  }

  private SmtExpr buildSmtCallExpr(ExprCall exprCall, SmtEnv smtEnv)
  {
    Func func = exprCall.fun;

    FunctionDeclaration function = translator.getFuncTranslation(func);

    List<SmtExpr> arguments = new ArrayList<>();

    for (int i = 0; i < exprCall.args.size(); i++)
    {
      SmtExpr expr = exprTranslator.translateExpr(exprCall.args.get(i), smtEnv);
      if (function.getSort(i) instanceof TupleSort)
      {
        expr = SmtUnaryExpr.Op.CHOOSE.make(expr);
      }
      arguments.add(expr);
    }

    SmtCallExpr callExpr = new SmtCallExpr(function, arguments);
    return callExpr;
  }
}
