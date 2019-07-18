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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.PLUS, environment);
        }
        else if (funcName.equals("integer/minus") || funcName.equals("integer/sub"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MINUS, environment);
        }
        else if (funcName.equals("integer/mul"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MULTIPLY, environment);
        }
        else if (funcName.equals("integer/div"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.DIVIDE, environment);
        }
        else if (funcName.equals("integer/rem"))
        {
            return translateArithmetic(argExprs.get(0), argExprs.get(1), BinaryExpression.Op.MOD, environment);
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

    public Expression translateArithmetic(Expression A, Expression B, BinaryExpression.Op op, Environment environment)
    {

        A = convertIntConstantToSet(A);

        B = convertIntConstantToSet(B);

        // for all x, y : uninterpretedInt. x in A and y in B implies
        // exists z :uninterpretedInt. (x, y, z) in operation


        if (A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = translator.handleIntConstant(A);
        }

        if (B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = translator.handleIntConstant(B);
        }

        Expression newA = A;
        Expression newB = B;

        // add variables in the environment as arguments to the result function
        LinkedHashMap<String, Expression> argumentsMap = environment.getVariables();
        List<Sort> argumentSorts = new ArrayList<>();
        List<Expression> arguments = new ArrayList<>();
        List<VariableDeclaration> quantifiedArguments = new ArrayList<>();
        for (Map.Entry<String, Expression> argument : argumentsMap.entrySet())
        {
            arguments.add(argument.getValue());
            Variable variable = (Variable) argument.getValue();
            Sort sort = variable.getSort();
            argumentSorts.add(sort);

            // handle set sorts differently to avoid sets quantifiers
            if (sort instanceof SetSort)
            {
                Sort elementSort = ((SetSort) sort).elementSort;
                VariableDeclaration tuple = new VariableDeclaration(variable.getName(), elementSort);
                quantifiedArguments.add(tuple);
                Expression singleton = UnaryExpression.Op.SINGLETON.make(tuple.getVariable());
                newA = newA.replace(argument.getValue(), singleton);
                newB = newB.replace(argument.getValue(), singleton);
                Expression constraint = ((VariableDeclaration) variable.getDeclaration()).getConstraint();
                if (constraint != null)
                {
                    constraint = constraint.replace(variable, singleton);
                }
                tuple.setConstraint(constraint);
            }
            else if (sort instanceof TupleSort || sort instanceof UninterpretedSort)
            {
                quantifiedArguments.add((VariableDeclaration) variable.getDeclaration());
            }
            else
            {
                throw new UnsupportedOperationException();
            }
        }

        FunctionDeclaration result = new FunctionDeclaration(TranslatorUtils.getFreshName(), argumentSorts, AbstractTranslator.setOfUninterpretedIntTuple);
        translator.smtProgram.addFunction(result);

        Expression resultExpression;
        if (result.getInputSorts().size() > 0)
        {
            resultExpression = new FunctionCallExpression(result, arguments);
        }
        else
        {
            resultExpression = result.getVariable();
        }

        VariableDeclaration x = new VariableDeclaration("__x__", AbstractTranslator.uninterpretedInt);
        VariableDeclaration y = new VariableDeclaration("__y__", AbstractTranslator.uninterpretedInt);
        VariableDeclaration z = new VariableDeclaration("__z__", AbstractTranslator.uninterpretedInt);

        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression zTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getVariable());

        Expression xValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, z.getVariable());

        Expression xMember = BinaryExpression.Op.MEMBER.make(xTuple, A);
        Expression yMember = BinaryExpression.Op.MEMBER.make(yTuple, B);
        Expression zMember = BinaryExpression.Op.MEMBER.make(zTuple, resultExpression);

        Expression xyOperation = op.make(xValue, yValue);
        Expression equal = BinaryExpression.Op.EQ.make(xyOperation, zValue);

        Expression and1 = MultiArityExpression.Op.AND.make(xMember, yMember);
        Expression and2 = MultiArityExpression.Op.AND.make(equal, and1);
        Expression exists1 = QuantifiedExpression.Op.EXISTS.make(and2, x, y);
        Expression argumentConstraints = BoolConstant.True;
        for (VariableDeclaration declaration : quantifiedArguments)
        {
            if (declaration.getConstraint() != null)
            {
                argumentConstraints = MultiArityExpression.Op.AND.make(argumentConstraints, declaration.getConstraint());
            }
        }
        Expression antecedent1 = MultiArityExpression.Op.AND.make(argumentConstraints, zMember);
        Expression implies1 = BinaryExpression.Op.IMPLIES.make(antecedent1, exists1);
        List<VariableDeclaration> quantifiers1 = new ArrayList<>(quantifiedArguments);
        quantifiers1.add(z);
        Expression forall1 = QuantifiedExpression.Op.FORALL.make(implies1, quantifiers1);

        Assertion assertion1 = new Assertion(String.format("%1$s %2$s %3$s axiom1", op, A, B), forall1);
        translator.smtProgram.addAssertion(assertion1);

        Expression and3 = MultiArityExpression.Op.AND.make(equal, zMember);
        Expression exists2 = QuantifiedExpression.Op.EXISTS.make(and3, z);

        Expression antecedent2 = MultiArityExpression.Op.AND.make(argumentConstraints, and1);

        Expression implies2 = BinaryExpression.Op.IMPLIES.make(antecedent2, exists2);
        List<VariableDeclaration> quantifiers2 = new ArrayList<>(quantifiedArguments);
        quantifiers2.add(x);
        quantifiers2.add(y);
        Expression forall2 = QuantifiedExpression.Op.FORALL.make(implies2, quantifiers2);

        Assertion assertion2 = new Assertion(String.format("%1$s %2$s %3$s axiom2", op, A, B), forall2);
        translator.smtProgram.addAssertion(assertion2);

        return resultExpression;
    }

    private Expression convertIntConstantToSet(Expression A)
    {
        if (A instanceof IntConstant)
        {
            ConstantDeclaration uninterpretedInt = translator.getUninterpretedIntConstant((IntConstant) A);
            Expression tuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, uninterpretedInt.getVariable());
            A = UnaryExpression.Op.SINGLETON.make(tuple);
        }
        return A;
    }
}
