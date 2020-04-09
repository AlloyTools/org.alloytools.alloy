package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.ExprVar;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.smtAst.*;

public class ExprVarTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprVarTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    SmtExpr translateExprVar(ExprVar exprVar, Environment environment)
    {
        String name = exprVar.label;

        if(environment.containsKey(name))
        {
            SmtExpr variable = environment.get(name);

            if(variable.getSort() == AbstractTranslator.atomSort)
            {
                return SmtUnaryExpr.Op.SINGLETON.make(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, variable));
            }
            else if(variable.getSort() == AbstractTranslator.intSort)
            {
                return SmtUnaryExpr.Op.SINGLETON.make(new SmtMultiArityExpr(SmtMultiArityExpr.Op.MKTUPLE, variable));
            }
            else if(variable.getSort() instanceof TupleSort)
            {
                return SmtUnaryExpr.Op.SINGLETON.make(variable);
            }

            return variable;
        }
        else
        {
            //ToDo: review the semantics of "this" keyword
//            if(exprVar.toString().equals("this"))
//            {
//                Sig sig = exprVar.type().fold().get(0).get(0);
//                return translator.signaturesMap.get(sig).getVariable();
//            }
            throw new RuntimeException(String.format(" Could not find name %s in the environment", name));
        }
    }
}
