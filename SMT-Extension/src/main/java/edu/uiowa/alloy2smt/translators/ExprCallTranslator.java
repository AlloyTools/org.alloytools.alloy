package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.uiowa.alloy2smt.utils.AlloySettings;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.io.File;
import java.util.*;

public class ExprCallTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprCallTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        this.translator = exprTranslator.translator;
    }

    Expression translateExprCall(ExprCall exprCall, Environment environment)
    {
        String funcName = exprCall.fun.label;
        List<Expression> argExprs = new ArrayList<>();

        for (Expr e : exprCall.args)
        {
            argExprs.add(exprTranslator.translateExpr(e, environment));
        }

//        if (this.translator.funcNamesMap.containsKey(funcName))
//        {
//            return new FunctionCallExpression(translator.getFunctionFromAlloyName(funcName), argExprs);
//        }
//        else if (this.translator.setComprehensionFuncNameToInputsMap.containsKey(funcName))
//        {
//            return translateSetComprehensionFuncCallExpr(funcName, argExprs);
//        }
        if(exprCall.fun.pos.filename.contains("models/util/ordering.als".replace("/", File.separator)))
        {
            return new FunctionCallExpression(translator.functionsMap.get(funcName), argExprs);
        }
        else if (funcName.equals("integer/plus") || funcName.equals("integer/add"))
        {
            return translateArithmetic(exprCall, argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, environment);
        }
        else if (funcName.equals("integer/minus") || funcName.equals("integer/sub"))
        {
            return translateArithmetic(exprCall, argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MINUS, environment);
        }
        else if (funcName.equals("integer/mul"))
        {
            return translateArithmetic(exprCall, argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MULTIPLY, environment);
        }
        else if (funcName.equals("integer/div"))
        {
            return translateArithmetic(exprCall, argExprs.get(0), argExprs.get(1), BinaryExpression.Op.DIVIDE, environment);
        }
        else if (funcName.equals("integer/rem"))
        {
            return translateArithmetic(exprCall, argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MOD, environment);
        }
//        else if (translator.functionsMap.containsKey(funcName))
//        {
//            FunctionDeclaration function = translator.getFunction(funcName);
//            return new FunctionCallExpression(function, argExprs);
//        }
        else
        {
            Expr body = exprCall.fun.getBody();

            for (int i = 0; i < exprCall.args.size(); i++)
            {
                body = AlloyUtils.substituteExpr(body, exprCall.fun.get(i), exprCall.args.get(i));
            }
            Expression callExpression = exprTranslator.translateExpr(body, environment);
            return callExpression;
        }
    }

    public Expression translateArithmetic(ExprCall exprCall, Expression A, Expression B, BinaryExpression.Op op, Environment environment)
    {
        A = convertIntConstantToSet(A);

        B = convertIntConstantToSet(B);

        if (A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = translator.handleIntConstant(A);
        }

        if (B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = translator.handleIntConstant(B);
        }

        String freshName = TranslatorUtils.getFreshName(AbstractTranslator.setOfUninterpretedIntTuple);

        VariableDeclaration x = new VariableDeclaration("x", AbstractTranslator.uninterpretedInt, false);
        VariableDeclaration y = new VariableDeclaration("y", AbstractTranslator.uninterpretedInt, false);
        VariableDeclaration z = new VariableDeclaration("z", AbstractTranslator.uninterpretedInt, false);

        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression zTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getVariable());

        Expression xValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, z.getVariable());

        Expression xyOperation = op.make(xValue, yValue);
        Expression equal = BinaryExpression.Op.EQ.make(xyOperation, zValue);

        if(translator.alloySettings.integerSingletonsOnly)
        {
            // A= {x}, B = {y} => Result = {z} where z = (x operation y)
            Expression xSingleton = UnaryExpression.Op.SINGLETON.make(xTuple);
            Expression ySingleton = UnaryExpression.Op.SINGLETON.make(yTuple);
            Expression singletonA = BinaryExpression.Op.EQ.make(A, xSingleton);
            Expression singletonB = BinaryExpression.Op.EQ.make(B, ySingleton);

            Expression and = MultiArityExpression.Op.AND.make(equal, singletonA, singletonB);

            QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(and, x, y, z);
            environment.addAuxiliaryFormula(exists);
            return z.getVariable();
        }

        VariableDeclaration result = new VariableDeclaration(freshName, AbstractTranslator.setOfUninterpretedIntTuple, false);
        Expression resultExpression = result.getVariable();

        // for all z : uninterpretedInt. x in Result implies
        // exists x, y :uninterpretedInt. x in A and y in B and (x, y, z) in operation

        Expression xMember = BinaryExpression.Op.MEMBER.make(xTuple, A);
        Expression yMember = BinaryExpression.Op.MEMBER.make(yTuple, B);
        Expression zMember = BinaryExpression.Op.MEMBER.make(zTuple, resultExpression);

        Expression xyMember = MultiArityExpression.Op.AND.make(xMember, yMember);
        Expression and2 = MultiArityExpression.Op.AND.make(equal, xyMember);
        Expression exists1 = QuantifiedExpression.Op.EXISTS.make(and2, x, y);

        Expression implies1 = BinaryExpression.Op.IMPLIES.make(zMember, exists1);
        Expression axiom1 = QuantifiedExpression.Op.FORALL.make(implies1, z);


        // for all x, y : uninterpretedInt. x in A and y in B implies
        // exists z :uninterpretedInt. x in Result and (x, y, z) in operation

        Expression and3 = MultiArityExpression.Op.AND.make(equal, zMember);
        Expression exists2 = QuantifiedExpression.Op.EXISTS.make(and3, z);

        Expression implies2 = BinaryExpression.Op.IMPLIES.make(xyMember, exists2);
        Expression axiom2 = QuantifiedExpression.Op.FORALL.make(implies2, x, y);

        Expression axioms = MultiArityExpression.Op.AND.make(axiom1, axiom2);
        QuantifiedExpression exists = QuantifiedExpression.Op.EXISTS.make(axioms, result);
        environment.addAuxiliaryFormula(exists);

        return resultExpression;
    }

    private Expression convertIntConstantToSet(Expression A)
    {
        if (A instanceof IntConstant)
        {
            ConstantDeclaration uninterpretedInt = translator.getUninterpretedIntConstant((IntConstant) A);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            if(translator.alloySettings.integerSingletonsOnly)
            {
                A = UnaryExpression.Op.SINGLETON.make(tuple);
            }
            else
            {
                A = tuple;
            }
        }
        return A;
    }
}
