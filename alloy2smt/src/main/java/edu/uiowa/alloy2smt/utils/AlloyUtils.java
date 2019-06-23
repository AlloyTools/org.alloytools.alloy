package edu.uiowa.alloy2smt.utils;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.uiowa.alloy2smt.Utils;
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

    public static List<CommandResult> runAlloyFileTimeout(int timeout, String fileName, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task(timeout);
        return task.run(translation, includeScope);
    }


    public static List<CommandResult> runAlloyFile(String fileName, boolean includeScope) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope);
    }

    public static CommandResult runAlloyFile(String fileName, boolean includeScope, int commandIndex) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task();
        return task.run(translation, includeScope, commandIndex);
    }

    public static CommandResult runAlloyFileTimeout(int timeout, String fileName, boolean includeScope, int commandIndex) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task(timeout);
        return task.run(translation, includeScope, commandIndex);
    }

    public static FunctionDefinition getFunctionDefinition(CommandResult commandResult, String name)
    {
        return TranslatorUtils.getFunctionDefinition(commandResult.smtModel, name);
    }

    public static List<Sort> getExprSorts(Expr expr)
    {
        List<Sort> sorts = new ArrayList<>();
        // get the first list of types from the fold function
        for(Sig.PrimSig sig : expr.type().fold().get(0))
        {
            if(sig.type().is_int())
            {
                sorts.add(AbstractTranslator.uninterpretedInt);
            }
            else
            {
                sorts.add(AbstractTranslator.atomSort);
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
            return BinaryExpression.Op.SUBSET.make(declaration.getVariable(), rightSetExpression);
        }
        if(declaration.getSort() instanceof TupleSort)
        {
            return BinaryExpression.Op.MEMBER.make(declaration.getVariable(), rightSetExpression);
        }
        if((declaration.getSort() instanceof UninterpretedSort) || (declaration.getSort() instanceof IntSort))
        {
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, declaration.getVariable());
            return BinaryExpression.Op.MEMBER.make(tuple, rightSetExpression);
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
            singleton = UnaryExpression.Op.SINGLETON.make(tuple);
        }
        else if(variable.getDeclaration().getSort() instanceof TupleSort)
        {
            singleton = UnaryExpression.Op.SINGLETON.make(variable);
        }
        else
        {
            throw new UnsupportedOperationException("Unexpected!");
        }
        return singleton;
    }

    public static Expression mkSingletonOutOfAtoms(List<Expression> atomExprs)
    {
        MultiArityExpression tuple      = MultiArityExpression.Op.MKTUPLE.make(atomExprs);
        UnaryExpression      singleton  = UnaryExpression.Op.SINGLETON.make(tuple);
        return singleton;
    }

    public static Expression mkSingletonOutOfTuple(Expression tupleExpr)
    {
        UnaryExpression      singleton  = UnaryExpression.Op.SINGLETON.make(tupleExpr);
        return singleton;
    }

    public static List<Expression> getFunctionCallArguments(List<VariableDeclaration> quantifiedArguments,
                                                          Map<String, Expression> argumentsMap)
    {
        List<Expression> expressions = new ArrayList<>();
        for (VariableDeclaration declaration: quantifiedArguments)
        {
            if(declaration.getSort().equals(argumentsMap.get(declaration.getName()).getSort()))
            {
                expressions.add(declaration.getVariable());
            }
            else
            {
                expressions.add(UnaryExpression.Op.SINGLETON.make(declaration.getVariable()));
            }
        }
        return expressions;
    }
}
