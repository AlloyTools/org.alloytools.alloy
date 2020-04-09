package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
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

    public Environment translateDecl(Decl decl, Environment parent)
    {
        List<Pair<Declaration, SmtExpr>> declarations = new ArrayList<>();

        Environment environment = new Environment(parent);

        for (ExprHasName name: decl.names)
        {
            Decl individualDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2, Collections.singletonList(name), decl.expr);
            environment = translateIndividualDecl(decl, environment);
        }

        //ToDo: disjoint

        //ToDo: disjoint2

        return environment;
    }

    public Environment translateIndividualDecl(Decl decl, Environment environment)
    {
        ExprHasName name = decl.names.get(0);
        List<Sort> sorts = AlloyUtils.getExprSorts(decl.expr);
        Sort sort;
        if(decl.expr instanceof ExprUnary && ((ExprUnary) decl.expr).op == ExprUnary.Op.ONEOF)
        {
            // for singletons quantifiers over the element sort
            sort = ((SetSort)sorts.get(0)).elementSort;
        }
        else
        {
            sort = sorts.get(0);
        }

        SmtVariable smtVariable = new SmtVariable(name.label, sort, true);
        SmtExpr set = exprTranslator.translateExpr(decl.expr, environment);
        SmtExpr memberOrSubset;
        if(sort instanceof SetSort)
        {
            memberOrSubset = SmtBinaryExpr.Op.SUBSET.make(smtVariable.getVariable(), set);
        }
        else
        {
            memberOrSubset = SmtBinaryExpr.Op.MEMBER.make(smtVariable.getVariable(), set);
        }

        smtVariable.setConstraint(memberOrSubset);
        environment.put(smtVariable.getName(), smtVariable.getVariable());
        return environment;
    }
}
