package edu.uiowa.alloy2smt.utils;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.Utils;
import edu.uiowa.alloy2smt.translators.Translation;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Formatter;
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

    public synchronized static CommandResult runAlloyFile(String fileName, boolean includeScope, int commandIndex) throws Exception
    {
        Translation translation = Utils.translateFromFile(fileName);
        Cvc4Task task = new Cvc4Task();
        CommandResult result =  task.run(translation, includeScope, commandIndex);
            /*
             id_lock.acquire()
            app.unique_id = app.unique_id + 1
            app.robots_dictionary[app.unique_id] = None
            client_directory = app.upload_directory + '/' + str(app.unique_id)
            if not os.path.exists(client_directory):
                os.makedirs(client_directory)
            id_lock.release()
            return jsonify({'id': app.unique_id})
             */
            int index = 0;
            String smtFile = fileName.replace(".als", "") + "_" + index + "_" + result.satResult + ".smt2";
            while(Files.exists(Paths.get(smtFile)))
            {
                index ++;
                smtFile = fileName.replace(".als", "") + "_" + index + "_" + result.satResult + ".smt2";
            }

            try (Formatter formatter = new Formatter(smtFile))
            {
                if(result.satResult.equals("sat"))
                {
                    formatter.format("%s\n", "; EXPECT: sat");
                }
                if(result.satResult.equals("unsat"))
                {
                    formatter.format("%s\n", "; EXPECT: unsat");
                }
                formatter.format("%s\n", result.smtProgram);
            }

        return result;
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

    public static Expr substituteExpr(Expr body, ExprVar oldExpr, Expr newExpr)
    {
        if(body instanceof ExprVar)
        {
            if(body.equals(oldExpr))
            {
                return newExpr;
            }
            else
            {
                return body;
            }
        }

        if(body instanceof ExprConstant)
        {
            return body;
        }

        if(body instanceof Sig || body instanceof Sig.Field)
        {
            return body;
        }

        if(body instanceof ExprUnary)
        {
            ExprUnary unary = (ExprUnary) body;
            Expr sub = substituteExpr(unary.sub, oldExpr, newExpr);
            return unary.op.make(unary.pos, sub);
        }

        if(body instanceof ExprBinary)
        {
            ExprBinary binary = (ExprBinary) body;
            Expr left = substituteExpr(binary.left, oldExpr, newExpr);
            Expr right = substituteExpr(binary.right, oldExpr, newExpr);
            return binary.op.make(binary.pos, binary.closingBracket, left, right);
        }

        if(body instanceof ExprQt)
        {
            ExprQt qt = (ExprQt) body;
            Expr sub = qt.sub;
            List<Decl> declList = new ArrayList<>();

            for (Decl decl : qt.decls)
            {
                List<ExprVar> variables = new ArrayList<>();
                for (ExprHasName name : decl.names)
                {
                    // return the body if the oldExpr is a quantifier
                    if(oldExpr.label.equals(name.label))
                    {
                        return body;
                    }

                    // change the quantifier name if newExpr contains a free variable with the same name
                    if(containsFreeVaraible((ExprVar) name, newExpr))
                    {
                        ExprVar newName = ExprVar.make(name.pos, TranslatorUtils.getFreshName(null));
                        sub = substituteExpr(sub, (ExprVar) name, newName);
                        variables.add(newName);
                    }
                    else
                    {
                        variables.add((ExprVar) name);
                    }
                }

                Expr declaredExpr = decl.expr;
                declaredExpr = substituteExpr(declaredExpr, oldExpr, newExpr);

                Decl newDecl = new Decl(decl.isPrivate, decl.disjoint, decl.disjoint2,
                        variables, declaredExpr);
                declList.add(newDecl);
            }

            sub = substituteExpr(sub, oldExpr, newExpr);
            Expr newQt = qt.op.make(qt.pos, qt.closingBracket, declList, sub);
            return newQt;
        }

        if(body instanceof ExprList)
        {
            ExprList list = (ExprList) body;

            List<Expr> arguments = new ArrayList<>();
            for (Expr expr: list.args)
            {
                Expr newArgument = substituteExpr(expr, oldExpr, newExpr);
                arguments.add(newArgument);
            }

            return ExprList.make(list.pos, list.closingBracket, list.op, arguments);
        }

        if(body instanceof ExprLet)
        {
            // first expand the let body

            ExprLet let = (ExprLet) body;

            Expr letExpanded = substituteExpr(let.sub, let.var, let.expr);
            Expr newLet = substituteExpr(letExpanded, oldExpr, newExpr);
            return newLet;
        }

        if(body instanceof ExprITE)
        {
            ExprITE ite = (ExprITE) body;
            Expr cond = substituteExpr(ite.cond, oldExpr, newExpr);
            Expr left = substituteExpr(ite.left, oldExpr, newExpr);
            Expr right = substituteExpr(ite.right, oldExpr, newExpr);
            return ExprITE.make(ite.pos, cond, left, right);
        }

        if(body instanceof ExprCall)
        {
            ExprCall call = (ExprCall) body;

            List<Expr> arguments = new ArrayList<>();
            for (Expr expr: call.args)
            {
                Expr newArgument = substituteExpr(expr, oldExpr, newExpr);
                arguments.add(newArgument);
            }

            return ExprCall.make(call.pos, call.closingBracket, call.fun, arguments, 0);
        }

        throw new UnsupportedOperationException();
    }

    private static boolean containsFreeVaraible(ExprVar variable, Expr expr)
    {
        if(expr instanceof ExprVar)
        {
            return variable.label.equals(((ExprVar) expr).label);
        }

        if(expr instanceof Sig || expr instanceof Sig.Field)
        {
            return false;
        }

        if(expr instanceof ExprConstant)
        {
            return false;
        }

        if(expr instanceof ExprUnary)
        {
            return containsFreeVaraible(variable, ((ExprUnary) expr).sub);
        }

        if(expr instanceof ExprBinary)
        {
            boolean left = containsFreeVaraible(variable, ((ExprBinary) expr).left);
            boolean right = containsFreeVaraible(variable, ((ExprBinary) expr).right);
            return left || right;
        }

        if(expr instanceof ExprQt)
        {
            for (Decl decl : ((ExprQt) expr).decls)
            {
                for (ExprHasName name : decl.names)
                {
                    if(name.label.equals(variable.label))
                    {
                        return false;
                    }
                }
            }
            return containsFreeVaraible(variable, ((ExprQt) expr).sub);
        }

        if(expr instanceof ExprList)
        {
            ExprList list = (ExprList) expr;

            for (Expr argument: list.args)
            {
               if(containsFreeVaraible(variable, argument))
               {
                   return true;
               }
            }

            return false;
        }

        if(expr instanceof ExprLet)
        {
            if(((ExprLet) expr).var.label.equals(variable.label))
            {
                return false;
            }

            boolean  exprBoolean = containsFreeVaraible(variable, ((ExprLet) expr).expr);
            boolean subBoolean = containsFreeVaraible(variable, ((ExprLet) expr).sub);
            return exprBoolean || subBoolean;
        }

        if(expr instanceof ExprITE)
        {
            ExprITE ite = (ExprITE) expr;
            boolean cond = containsFreeVaraible(variable, ite.cond);
            boolean left = containsFreeVaraible(variable, ite.left);
            boolean right = containsFreeVaraible(variable, ite.right);
            return cond || left || right;
        }

        if(expr instanceof ExprCall)
        {
            ExprCall call = (ExprCall) expr;

            for (Expr argument: call.args)
            {
                if(containsFreeVaraible(variable, argument))
                {
                    return true;
                }
            }

            return false;
        }

        throw new UnsupportedOperationException();
    }

    public static Expr removeMultiplicity(Decl decl)
    {
        return removeMultiplicity(decl.expr);
    }

    private static Expr removeMultiplicity(Expr expr)
    {
        if(expr instanceof ExprVar)
        {
            return expr;
        }

        if(expr instanceof Sig || expr instanceof Sig.Field)
        {
            return expr;
        }

        if(expr instanceof ExprConstant)
        {
            return expr;
        }

        if(expr instanceof ExprUnary)
        {
            return ((ExprUnary) expr).sub;
        }

        if(expr instanceof ExprBinary)
        {
            Expr left = ((ExprBinary) expr).left;
            Expr right = ((ExprBinary) expr).right;
            return ExprBinary.Op.ARROW.make(expr.pos, expr.closingBracket, left, right);
        }
        throw new UnsupportedOperationException();
    }
}
