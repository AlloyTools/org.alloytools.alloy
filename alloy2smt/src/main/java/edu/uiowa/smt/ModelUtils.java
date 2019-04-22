package edu.uiowa.smt;

import edu.uiowa.smt.smtAst.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

public class ModelUtils
{
    public static int getInt(FunctionDefinition definition)
    {
        return getInt(definition.expression);
    }

    public static int getInt(Expression expression)
    {
        UnaryExpression unary =  (UnaryExpression) expression;
        if(unary.getOP() == UnaryExpression.Op.EMPTYSET)
        {
            return 0; // zero is equivalent to an empty set
        }
        assert( UnaryExpression.Op.SINGLETON ==  unary.getOP());
        MultiArityExpression tuple =  (MultiArityExpression) unary.getExpression();
        assert(MultiArityExpression.Op.MKTUPLE == tuple.getOp());
        IntConstant constant = (IntConstant) tuple.getExpressions().get(0);
        return Integer.parseInt(constant.getValue());
    }

    public static Set<Integer> getIntSet(FunctionDefinition definition)
    {
        return getIntSet(definition.getExpression());
    }

    public static Set<Integer> getIntSet(Expression expression)
    {
        if(expression instanceof UnaryExpression)
        {
            return new HashSet<>(Arrays.asList(getInt(expression)));
        }
        BinaryExpression binary = (BinaryExpression) expression;
        Set<Integer> set = new HashSet<>();
        assert(binary.getOp() == BinaryExpression.Op.UNION);
        set.addAll(getIntSet(binary.getLhsExpr()));
        set.addAll(getIntSet(binary.getRhsExpr()));
        return set;
    }

    public static FunctionDefinition getFunctionDefinition(SmtModel smtModel, String name)
    {
        FunctionDefinition definition = (FunctionDefinition) smtModel
                .getFunctions().stream()
                .filter(f -> f.getName().equals(name)).findFirst().get();
        definition = smtModel.evaluateUninterpretedInt(definition);
        return definition;
    }
}
