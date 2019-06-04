package edu.uiowa.alloy2smt.utils;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.translators.Alloy2SmtTranslator;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class AlloyUtils
{
    public static List<CommandResult> runAlloyString(String alloy, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translate(alloy);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope);
    }

    public static List<CommandResult> runAlloyFile(String fileName, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope);
    }

    public static FunctionDefinition getFunctionDefinition(CommandResult commandResult, String name)
    {
        return TranslatorUtils.getFunctionDefinition(commandResult.smtModel, name);
    }

    public static List<Sort> getExprSorts(Expr expr)
    {
        List<Sort> sorts = new ArrayList<>();
        for(List<Sig.PrimSig> sigs : expr.type().fold())
        {
            for(Sig.PrimSig s : sigs)
            {
                if(s.type().is_int())
                {
                    sorts.add(AbstractTranslator.uninterpretedInt);
                }
                else
                {
                    sorts.add(AbstractTranslator.atomSort);
                }
            }
        }
        return sorts;
    }

    public static BinaryExpression getMemberExpression(Map<VariableDeclaration, Expression> variableToSetMap, int index)
    {
        VariableDeclaration declaration = (new ArrayList<>(variableToSetMap.keySet())).get(index);
        Expression rightSetExpression = variableToSetMap.get(declaration);
        if(declaration.getSort() instanceof SetSort)
        {
            return new BinaryExpression(declaration.getVariable(), BinaryExpression.Op.SUBSET, rightSetExpression);
        }
        if(declaration.getSort() instanceof TupleSort)
        {
            return new BinaryExpression(declaration.getVariable(), BinaryExpression.Op.MEMBER, rightSetExpression);
        }
        if((declaration.getSort() instanceof UninterpretedSort) || (declaration.getSort() instanceof IntSort))
        {
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, declaration.getVariable());
            return new BinaryExpression(tuple, BinaryExpression.Op.MEMBER, rightSetExpression);
        }

        throw new UnsupportedOperationException(String.format("%s", declaration.getSort()));
    }

    public static Expression mkSingletonOutOfTupleOrAtom(Variable variable)
    {
        UnaryExpression singleton = null;

        if((variable.getDeclaration().getSort() instanceof UninterpretedSort) ||
                variable.getDeclaration().getSort() instanceof IntSort)
        {
            MultiArityExpression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, variable);
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        }
        else if(variable.getDeclaration().getSort() instanceof TupleSort)
        {
            singleton = new UnaryExpression(UnaryExpression.Op.SINGLETON, variable);
        }
        else
        {
            throw new UnsupportedOperationException("Unexpected!");
        }
        return singleton;
    }

    public static Expression mkSingletonOutOfAtoms(List<Expression> atomExprs)
    {
        MultiArityExpression tuple      = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, atomExprs);
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tuple);
        return singleton;
    }

    public static Expression mkSingletonOutOfTuple(Expression tupleExpr)
    {
        UnaryExpression      singleton  = new UnaryExpression(UnaryExpression.Op.SINGLETON, tupleExpr);
        return singleton;
    }
}
