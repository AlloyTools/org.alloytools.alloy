package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class ExprBinaryTranslator
{
    final ExprTranslator exprTranslator;
    final Alloy2SmtTranslator translator;

    public ExprBinaryTranslator(ExprTranslator exprTranslator)
    {
        this.exprTranslator = exprTranslator;
        translator = exprTranslator.translator;
    }

    Expression translateExprBinary(ExprBinary expr, Environment environment)
    {
        switch (expr.op)
        {
            case ARROW:
                return translateArrow(expr, environment);
            case ANY_ARROW_SOME:
                return translateAnyArrowSome(expr, environment);
            case ANY_ARROW_ONE:
                return translateAnyArrowOne(expr, environment);
            case ANY_ARROW_LONE:
                return translateAnyArrowLone(expr, environment);
            case SOME_ARROW_ANY:
                return translateSomeArrowAny(expr, environment);
            case SOME_ARROW_SOME:
                return translateSomeArrowSome(expr, environment);
            case SOME_ARROW_ONE:
                return translateSomeArrowOne(expr, environment);
            case SOME_ARROW_LONE:
                return translateSomeArrowLone(expr, environment);
            case ONE_ARROW_ANY:
                return translateOneArrowAny(expr, environment);
            case ONE_ARROW_SOME:
                return translateOneArrowSome(expr, environment);
            case ONE_ARROW_ONE:
                return translateOneArrowOne(expr, environment);
            case ONE_ARROW_LONE:
                return translateOneArrowLone(expr, environment);
            case LONE_ARROW_ANY:
                return translateLoneArrowAny(expr, environment);
            case LONE_ARROW_SOME:
                return translateLoneArrowSome(expr, environment);
            case LONE_ARROW_ONE:
                return translateLoneArrowOne(expr, environment);
            case LONE_ARROW_LONE:
                return translateLoneArrowLone(expr, environment);
            case ISSEQ_ARROW_LONE:
                throw new UnsupportedOperationException();

                // Relational operators
            case JOIN:
                return translateJoin(expr, environment);
            case DOMAIN:
                return translateDomainRestriction(expr, environment);
            case RANGE:
                return translateRangeRestriction(expr, environment);
            case INTERSECT:
                return translateSetOperation(expr, BinaryExpression.Op.INTERSECTION, environment);
            case PLUSPLUS:
                return translatePlusPlus(expr, environment);
            case EQUALS:
                return translateEqComparison(expr, BinaryExpression.Op.EQ, environment);
            case NOT_EQUALS:
                return UnaryExpression.Op.NOT.make(translateEqComparison(expr, BinaryExpression.Op.EQ, environment));

            // Set op
            case PLUS:
                return translateSetOperation(expr, BinaryExpression.Op.UNION, environment);
            case MINUS:
                return translateSetOperation(expr, BinaryExpression.Op.SETMINUS, environment);

            // Arithmetic operators            
            case IPLUS:
                return translateArithmetic(expr, BinaryExpression.Op.PLUS, environment);
            case IMINUS:
                return translateArithmetic(expr, BinaryExpression.Op.MINUS, environment);
            case MUL:
                return translateArithmetic(expr, BinaryExpression.Op.MULTIPLY, environment);
            case DIV:
                return translateArithmetic(expr, BinaryExpression.Op.DIVIDE, environment);
            case REM:
                return translateArithmetic(expr, BinaryExpression.Op.MOD, environment);
            // Comparison operators
            case LT:
                return translateComparison(expr, BinaryExpression.Op.LT, environment);
            case LTE:
                return translateComparison(expr, BinaryExpression.Op.LTE, environment);
            case GT:
                return translateComparison(expr, BinaryExpression.Op.GT, environment);
            case GTE:
                return translateComparison(expr, BinaryExpression.Op.GTE, environment);
            case IN:
                return translateSubsetOperation(expr, environment);
            case NOT_IN:
                return UnaryExpression.Op.NOT.make(translateSubsetOperation(expr, environment));
            case IMPLIES:
                return translateImplies(expr, environment);
            case AND:
                return translateAnd(expr, environment);
            case OR:
                return translateOr(expr, environment);
            case IFF:
                return translateEqComparison(expr, BinaryExpression.Op.EQ, environment);
            case NOT_LT:
                return translateComparison(expr, BinaryExpression.Op.GTE, environment);
            case NOT_LTE:
                return translateComparison(expr, BinaryExpression.Op.GT, environment);
            case NOT_GT:
                return translateComparison(expr, BinaryExpression.Op.LTE, environment);
            case NOT_GTE:
                return translateComparison(expr, BinaryExpression.Op.LT, environment);
            case SHL:
                throw new UnsupportedOperationException();
            case SHA:
                throw new UnsupportedOperationException();
            case SHR:
                throw new UnsupportedOperationException();
            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expression translateOneArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A one -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);


        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);


        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateOneArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);


        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A one -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(yMemberB, xyMember);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateOneArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A one -> set B
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllY);

        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateSomeArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A some -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);


        Expression existsXBody = MultiArityExpression.Op.AND.make(xMemberA, xyMember);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateAnyArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A set -> one B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet and
        //       forall v in B. v != y implies xv not in  multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateSomeArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A some -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        Expression existsYBody = MultiArityExpression.Op.AND.make(yMemberB, xyMember);
        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(xMemberA, xyMember);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(Arrays.asList(forAllX, forAllY, subset));

        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);
        return multiplicitySet.getVariable();
    }

    private Expression translateSomeArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A some -> set B
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        Expression existsXBody = MultiArityExpression.Op.AND.make(xMemberA, xyMember);
        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);

        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateAnyArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        // multiplicitySet subset of A set -> some B
        // and
        // forall x in A . exists y in B . xy in multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());

        Expression existsYBody = MultiArityExpression.Op.AND.make(yMemberB, xyMember);
        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);
        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);

        environment.addAuxiliaryFormula(existsSet);
        return multiplicitySet.getVariable();
    }

    private Expression translateOneArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);


        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A one -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B . exists x in A . xy in multiplicitySet and
        //       forall u in A. u != x implies uy not in  multiplicitySet


        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression lone = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, y), existsY);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, lone);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateSomeArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);


        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A some -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B . exists x in A . xy in multiplicitySet

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression lone = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, y), existsY);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, lone);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(xMemberA, xyMember);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, existsX);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateAnyArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A set -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)

        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression lone = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, y), existsY);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, lone);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateLoneArrowLone(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A lone -> lone B
        // and
        // forall x in A .
        //      (forall y in B. xy not in multiplicitySet)
        //      or
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression loneWest = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, y), existsY);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, loneWest);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression loneEast = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, x), existsX);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, loneEast);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateLoneArrowOne(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        VariableDeclaration v = new VariableDeclaration("v", BSort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);
        Expression vMemberB = BinaryExpression.Op.MEMBER.make(v.getVariable(), B);

        // multiplicitySet subset of A lone -> one B
        // and
        // forall x in A .
        //      (exists y in B . xy in multiplicitySet and
        //          forall v in B. v != y implies xv not in  multiplicitySet)
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression xvTuple = getTupleConcatenation(ASort, BSort, x, v);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression xvMember = BinaryExpression.Op.MEMBER.make(xvTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notXV = UnaryExpression.Op.NOT.make(xvMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);

        Expression vEqualY = BinaryExpression.Op.EQ.make(v.getVariable(), y.getVariable());
        Expression notVEqualY = UnaryExpression.Op.NOT.make(vEqualY);

        Expression vImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(vMemberB, notVEqualY), notXV);
        Expression forAllV = QuantifiedExpression.Op.FORALL.make(vImplies, v);

        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(yMemberB, xyMember), forAllV);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);

        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression loneEast = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, x), existsX);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, loneEast);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);


        return multiplicitySet.getVariable();
    }

    private Expression translateLoneArrowSome(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);


        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A lone -> some B
        // and
        // forall x in A .
        //      (exists y in B . xy in multiplicitySet
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);


        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);

        Expression existsYBody = MultiArityExpression.Op.AND.make(yMemberB, xyMember);

        Expression existsY = QuantifiedExpression.Op.EXISTS.make(existsYBody, y);
        Expression xImplies = BinaryExpression.Op.IMPLIES.make(xMemberA, existsY);
        Expression forAllX = QuantifiedExpression.Op.FORALL.make(xImplies, x);


        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression loneEast = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, x), existsX);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, loneEast);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllX, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression translateLoneArrowAny(ExprBinary expr, Environment environment)
    {
        SetSort sort = new SetSort(new TupleSort(AlloyUtils.getExprSorts(expr)));
        VariableDeclaration multiplicitySet = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);

        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);

        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        Expression subset = BinaryExpression.Op.SUBSET.make(multiplicitySet.getVariable(), product);

        SetSort ASort = (SetSort) A.getSort();
        SetSort BSort = (SetSort) B.getSort();

        VariableDeclaration x = new VariableDeclaration("x", ASort.elementSort, false);
        VariableDeclaration y = new VariableDeclaration("y", BSort.elementSort, false);
        Expression xMemberA = BinaryExpression.Op.MEMBER.make(x.getVariable(), A);
        Expression yMemberB = BinaryExpression.Op.MEMBER.make(y.getVariable(), B);

        VariableDeclaration u = new VariableDeclaration("u", ASort.elementSort, false);
        Expression uMemberA = BinaryExpression.Op.MEMBER.make(u.getVariable(), A);

        // multiplicitySet subset of A lone -> set B
        // and
        // forall y in B.
        //      (forall x in A. xy not in multiplicitySet)
        //      or
        //      (exists x in A . xy in multiplicitySet and
        //          forall u in A. u != x implies uy not in  multiplicitySet)


        Expression xyTuple = getTupleConcatenation(ASort, BSort, x, y);
        Expression uyTuple = getTupleConcatenation(ASort, BSort, u, y);

        Expression xyMember = BinaryExpression.Op.MEMBER.make(xyTuple, multiplicitySet.getVariable());
        Expression uyMember = BinaryExpression.Op.MEMBER.make(uyTuple, multiplicitySet.getVariable());

        Expression notXY = UnaryExpression.Op.NOT.make(xyMember);
        Expression notUY = UnaryExpression.Op.NOT.make(uyMember);


        Expression uEqualX = BinaryExpression.Op.EQ.make(u.getVariable(), x.getVariable());
        Expression notUEqualX = UnaryExpression.Op.NOT.make(uEqualX);

        Expression uImplies = BinaryExpression.Op.IMPLIES.make(MultiArityExpression.Op.AND.make(uMemberA, notUEqualX), notUY);
        Expression forAllU = QuantifiedExpression.Op.FORALL.make(uImplies, u);
        Expression existsXBody = MultiArityExpression.Op.AND.make(MultiArityExpression.Op.AND.make(xMemberA, xyMember), forAllU);

        Expression existsX = QuantifiedExpression.Op.EXISTS.make(existsXBody, x);
        Expression loneEast = MultiArityExpression.Op.OR.make(QuantifiedExpression.Op.FORALL.make(notXY, x), existsX);
        Expression yImplies = BinaryExpression.Op.IMPLIES.make(yMemberB, loneEast);
        Expression forAllY = QuantifiedExpression.Op.FORALL.make(yImplies, y);

        Expression and = MultiArityExpression.Op.AND.make(subset, forAllY);
        QuantifiedExpression existsSet = QuantifiedExpression.Op.EXISTS.make(and, multiplicitySet);
        environment.addAuxiliaryFormula(existsSet);

        return multiplicitySet.getVariable();
    }

    private Expression getTupleConcatenation(SetSort ASort, SetSort BSort, VariableDeclaration x, VariableDeclaration y)
    {
        List<Expression> tupleElements = new ArrayList<>();
        for (int i = 0; i < ((TupleSort) ASort.elementSort).elementSorts.size(); i++)
        {
            IntConstant index = IntConstant.getInstance(i);
            tupleElements.add(BinaryExpression.Op.TUPSEL.make(index, x.getVariable()));
        }

        for (int i = 0; i < ((TupleSort) BSort.elementSort).elementSorts.size(); i++)
        {
            IntConstant index = IntConstant.getInstance(i);
            tupleElements.add(BinaryExpression.Op.TUPSEL.make(index, y.getVariable()));
        }

        return MultiArityExpression.Op.MKTUPLE.make(tupleElements);
    }

    private Expression translateImplies(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        Expression A = exprTranslator.translateExpr(expr.left, environmentA);
        Expression B = exprTranslator.translateExpr(expr.right, environmentB);
        Expression implies = BinaryExpression.Op.IMPLIES.make(A, B);

        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(implies, environmentA);
        finalExpression = exprTranslator.translateAuxiliaryFormula(finalExpression, environmentB);
        return finalExpression;
    }

    private Expression translateAnd(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        Expression A = exprTranslator.translateExpr(expr.left, environmentA);
        Expression B = exprTranslator.translateExpr(expr.right, environmentB);
        Expression and = MultiArityExpression.Op.AND.make(A, B);

        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(and, environmentA);
        finalExpression = exprTranslator.translateAuxiliaryFormula(finalExpression, environmentB);
        return finalExpression;
    }

    private Expression translateOr(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        Expression A = exprTranslator.translateExpr(expr.left, environmentA);
        Expression B = exprTranslator.translateExpr(expr.right, environmentB);
        Expression or = MultiArityExpression.Op.OR.make(A, B);

        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(or, environmentA);
        finalExpression = exprTranslator.translateAuxiliaryFormula(finalExpression, environmentB);
        return finalExpression;
    }

    private Expression translateArrow(ExprBinary expr, Environment environment)
    {
        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);
        Expression product = BinaryExpression.Op.PRODUCT.make(A, B);
        return product;
    }

    private Expression translatePlusPlus(ExprBinary expr, Environment environment)
    {
        int rightExprArity = expr.right.type().arity();
        if (rightExprArity == 1)
        {
            // ++ is like a single + with arity 1 (i.e. is like a union)
            return translateSetOperation(expr, BinaryExpression.Op.UNION, environment);
        }
        else
        {
            Expression left = exprTranslator.translateExpr(expr.left, environment);
            Expression right = exprTranslator.translateExpr(expr.right, environment);
            Expression join = right;

            for (int i = 0; i < rightExprArity - 1; ++i)
            {
                join = BinaryExpression.Op.JOIN.make(join, exprTranslator.translator.univAtom.getVariable());
            }
            for (int i = 0; i < rightExprArity - 1; ++i)
            {
                join = BinaryExpression.Op.PRODUCT.make(join, exprTranslator.translator.univAtom.getVariable());
            }

            Expression intersection = BinaryExpression.Op.INTERSECTION.make(join, left);
            Expression difference = BinaryExpression.Op.SETMINUS.make(left, intersection);
            Expression union = BinaryExpression.Op.UNION.make(difference, right);

            return union;

        }
    }

    private Expression translateDomainRestriction(ExprBinary expr, Environment environment)
    {
        int arity = expr.right.type().arity();

        if (arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            Expression left = exprTranslator.translateExpr(expr.left, environment);
            Expression right = exprTranslator.translateExpr(expr.right, environment);

            // right type should be a set of tuples
            SetSort rightSort = (SetSort) right.getSort();
            TupleSort tuple = (TupleSort) rightSort.elementSort;
            for (int i = 1; i < arity; i++)
            {
                UninterpretedSort sort = (UninterpretedSort) tuple.elementSorts.get(i);
                if (sort.equals(AbstractTranslator.atomSort))
                {
                    left = BinaryExpression.Op.PRODUCT.make(left, translator.univAtom.getVariable());
                }
                else
                {
                    left = BinaryExpression.Op.PRODUCT.make(left, translator.univInt.getVariable());
                }
            }
            BinaryExpression intersection = BinaryExpression.Op.INTERSECTION.make(left, right);
            return intersection;
        }
    }

    private Expression translateRangeRestriction(ExprBinary expr, Environment environment)
    {
        int arity = expr.left.type().arity();

        if (arity <= 1)
        {
            // arity should be greater than one
            throw new UnsupportedOperationException();
        }
        else
        {
            Expression left = exprTranslator.translateExpr(expr.left, environment);
            Expression right = exprTranslator.translateExpr(expr.right, environment);

            // left type should be a set of tuples
            SetSort leftSort = (SetSort) left.getSort();
            TupleSort tuple = (TupleSort) leftSort.elementSort;
            for (int i = 0; i < arity - 1; i++)
            {
                UninterpretedSort sort = (UninterpretedSort) tuple.elementSorts.get(i);
                if (sort.equals(AbstractTranslator.atomSort))
                {
                    right = BinaryExpression.Op.PRODUCT.make(translator.univAtom.getVariable(), right);
                }
                else
                {
                    right = BinaryExpression.Op.PRODUCT.make(translator.univInt.getVariable(), right);
                }
            }

            BinaryExpression intersection = BinaryExpression.Op.INTERSECTION.make(left, right);

            return intersection;
        }
    }

    public Expression translateArithmetic(ExprBinary expr, BinaryExpression.Op op, Environment environment)
    {
        Expression leftExpr = exprTranslator.translateExpr(expr.left, environment);
        Expression rightExpr = exprTranslator.translateExpr(expr.right, environment);

        FunctionDeclaration result = new FunctionDeclaration(TranslatorUtils.getFreshName(AbstractTranslator.setOfUninterpretedIntTuple), AbstractTranslator.setOfUninterpretedIntTuple, false);
        exprTranslator.translator.smtProgram.addFunction(result);

        VariableDeclaration x = new VariableDeclaration("x", AbstractTranslator.uninterpretedInt, false);
        VariableDeclaration y = new VariableDeclaration("y", AbstractTranslator.uninterpretedInt, false);
        VariableDeclaration z = new VariableDeclaration("z", AbstractTranslator.uninterpretedInt, false);

        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression zTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, z.getVariable());

        Expression xValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, y.getVariable());
        Expression zValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, z.getVariable());

        Expression xMember = BinaryExpression.Op.MEMBER.make(xTuple, leftExpr);
        Expression yMember = BinaryExpression.Op.MEMBER.make(yTuple, rightExpr);
        Expression zMember = BinaryExpression.Op.MEMBER.make(zTuple, result.getVariable());

        Expression xyOperation = op.make(xValue, yValue);
        Expression equal = BinaryExpression.Op.EQ.make(xyOperation, zValue);

        Expression and1 = MultiArityExpression.Op.AND.make(xMember, yMember);
        Expression and2 = MultiArityExpression.Op.AND.make(equal, and1);
        Expression exists1 = QuantifiedExpression.Op.EXISTS.make(and2, x, y);
        Expression implies1 = BinaryExpression.Op.IMPLIES.make(zMember, exists1);
        Expression forall1 = QuantifiedExpression.Op.FORALL.make(implies1, z);

        Assertion assertion1 = AlloyUtils.getAssertion(Collections.singletonList(expr.pos),
                String.format("%1$s %2$s %3$s axiom1", op, leftExpr, rightExpr), forall1);
        exprTranslator.translator.smtProgram.addAssertion(assertion1);

        Expression and3 = BinaryExpression.Op.MEMBER.make(equal, zMember);
        Expression exists2 = QuantifiedExpression.Op.EXISTS.make(and3, z);

        Expression implies2 = BinaryExpression.Op.IMPLIES.make(and1, exists2);
        Expression forall2 = QuantifiedExpression.Op.FORALL.make(implies2, x, y);

        Assertion assertion2 = AlloyUtils.getAssertion(Collections.singletonList(expr.pos),
                String.format("%1$s %2$s %3$s axiom2", op, leftExpr, rightExpr), forall2);
        exprTranslator.translator.smtProgram.addAssertion(assertion2);

        return result.getVariable();
    }

    private Expression translateComparison(ExprBinary expr, BinaryExpression.Op op, Environment environment)
    {
        Expression comparisonExpr = null;

        // Right hand side is a expression and right hand side is a constant
        if (((expr.left instanceof ExprUnary) && ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                (expr.right instanceof ExprConstant)))
        {
            int n = ((ExprConstant) expr.right).num;
            int arity = ((ExprUnary) expr.left).sub.type().arity();
            Expression leftExpr = exprTranslator.translateExpr(((ExprUnary) expr.left).sub, environment);

            List<Expression> existentialBdVarExprs = new ArrayList<>();
            List<VariableDeclaration> existentialBdVars = new ArrayList<>();
            List<Sort> leftExprSorts = AlloyUtils.getExprSorts(((ExprUnary) expr.left).sub);

            switch (op)
            {
                case GT:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n + 1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n + 1);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression rightExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
                    }

                    // rightExpr + 1 <= leftExpr
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(rightExpr, leftExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case LT:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n - 1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n - 1);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression rightExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
                    }

                    // leftExpr <= rightExpr-1
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(leftExpr, rightExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case GTE:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression rightExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
                    }

                    // rightExpr <= leftExpr
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(rightExpr, leftExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case LTE:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(leftExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(leftExprSorts, arity, n);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression rightExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        rightExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        rightExpr = exprTranslator.mkEmptyRelationOfSort(leftExprSorts);
                    }

                    // rightExpr <= leftExpr
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(leftExpr, rightExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                default:
                    break;
            }
        }
        else if ((expr.right instanceof ExprUnary) && ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY &&
                (expr.left instanceof ExprConstant))
        {
            int n = ((ExprConstant) expr.left).num;
            int arity = ((ExprUnary) expr.right).sub.type().arity();
            Expression rightExpr = exprTranslator.translateExpr(((ExprUnary) expr.right).sub, environment);

            List<Expression> existentialBdVarExprs = new ArrayList<>();
            List<VariableDeclaration> existentialBdVars = new ArrayList<>();
            List<Sort> rightExprSorts = AlloyUtils.getExprSorts(((ExprUnary) expr.right).sub);

            switch (op)
            {
                case GT:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n + 1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n + 1);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression leftExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
                    }

                    // rightExpr + 1 <= leftExpr
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(rightExpr, leftExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case LT:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n - 1);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n - 1);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression leftExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
                    }

                    // leftExpr <= rightExpr-1
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(rightExpr, leftExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case GTE:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression leftExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
                    }

                    // rightExpr <= leftExpr
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(rightExpr, leftExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                case LTE:
                {
                    if (arity == 1)
                    {
                        existentialBdVars = exprTranslator.getBdVars(rightExprSorts.get(0), n);
                    }
                    else
                    {
                        existentialBdVars = exprTranslator.getBdTupleVars(rightExprSorts, arity, n);
                    }

                    for (VariableDeclaration bdVar : existentialBdVars)
                    {
                        existentialBdVarExprs.add(bdVar.getVariable());
                    }

                    // (distinct e1 e2 e3 ....)
                    Expression distElementsExpr = TranslatorUtils.makeDistinct(existentialBdVarExprs);

                    exprTranslator.translator.existentialBdVars.addAll(existentialBdVars);
                    if (exprTranslator.translator.auxExpr != null)
                    {
                        exprTranslator.translator.auxExpr = MultiArityExpression.Op.AND.make(exprTranslator.translator.auxExpr, distElementsExpr);
                    }
                    else
                    {
                        exprTranslator.translator.auxExpr = distElementsExpr;
                    }

                    Expression leftExpr;

                    if (existentialBdVarExprs.size() > 0)
                    {
                        leftExpr = exprTranslator.mkUnaryRelationOutOfAtomsOrTuples(existentialBdVarExprs);
                    }
                    else
                    {
                        leftExpr = exprTranslator.mkEmptyRelationOfSort(rightExprSorts);
                    }

                    // leftExpr <= rightExpr 
                    comparisonExpr = BinaryExpression.Op.SUBSET.make(leftExpr, rightExpr);
                    comparisonExpr = MultiArityExpression.Op.AND.make(comparisonExpr, exprTranslator.translator.auxExpr);

                    if (!exprTranslator.translator.existentialBdVars.isEmpty())
                    {
                        comparisonExpr = QuantifiedExpression.Op.EXISTS.make(comparisonExpr, exprTranslator.translator.existentialBdVars);
                    }
                    break;
                }
                default:
                    break;
            }
        }
        else
        {
            Expression leftExpr = exprTranslator.translateExpr(expr.left, environment);
            Expression rightExpr = exprTranslator.translateExpr(expr.right, environment);


            comparisonExpr = getComparison(op, leftExpr, rightExpr);
        }

        //ToDo: review the purpose of these 2 lines.
        exprTranslator.translator.auxExpr = null;
        exprTranslator.translator.existentialBdVars.clear();
        return comparisonExpr;
    }

    private Expression getComparison(BinaryExpression.Op op, Expression left, Expression right)
    {
        VariableDeclaration x = new VariableDeclaration("x", AbstractTranslator.uninterpretedInt, false);
        VariableDeclaration y = new VariableDeclaration("y", AbstractTranslator.uninterpretedInt, false);
        Expression xTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, x.getVariable());
        Expression yTuple = new MultiArityExpression(MultiArityExpression.Op.MKTUPLE, y.getVariable());
        Expression xSingleton = UnaryExpression.Op.SINGLETON.make(xTuple);
        Expression ySingleton = UnaryExpression.Op.SINGLETON.make(yTuple);
        Expression xValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, x.getVariable());
        Expression yValue = new FunctionCallExpression(AbstractTranslator.uninterpretedIntValue, y.getVariable());

        Expression relation1EqualsX = BinaryExpression.Op.EQ.make(xSingleton, left);
        Expression relation2EqualsY = BinaryExpression.Op.EQ.make(ySingleton, right);
        Expression and1 = MultiArityExpression.Op.AND.make(relation1EqualsX, relation2EqualsY);

        Expression comparison = op.make(xValue, yValue);
        Expression and2 = MultiArityExpression.Op.AND.make(and1, comparison);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(and2, Arrays.asList(x, y));

        //ToDo: remove these 2 lines
//        Assertion assertion = new Assertion(left + " " + op + " " + right , exists);
//        exprTranslator.translator.smtProgram.addAssertion(assertion);
        return exists;
    }

    private Expression translateEqComparison(ExprBinary expr, BinaryExpression.Op op, Environment environment)
    {

        if ((expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY) ||
                (expr.right instanceof ExprUnary &&
                        ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
        )
        {
            return translateCardinality(expr, op, environment);
        }

        Environment environmentA = new Environment(environment);
        Environment environmentB = new Environment(environment);
        Expression A = exprTranslator.translateExpr(expr.left, environmentA);
        Expression B = exprTranslator.translateExpr(expr.right, environmentB);

        A = TranslatorUtils.makeRelation(A);
        B = TranslatorUtils.makeRelation(B);

        if (A.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            A = exprTranslator.translator.handleIntConstant(A);
        }

        if (B.getSort().equals(AbstractTranslator.setOfIntSortTuple))
        {
            B = exprTranslator.translator.handleIntConstant(B);
        }

        Expression equality = BinaryExpression.Op.EQ.make(A, B);

        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(equality, environmentA);
        finalExpression = exprTranslator.translateAuxiliaryFormula(finalExpression, environmentB);
        return finalExpression;
    }

    private Expression translateCardinality(ExprBinary expr, BinaryExpression.Op op, Environment environment)
    {
        // CVC4 doesn't support comparison  between 2 cardinality expressions
        if
        (expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY
        )
        {
            throw new UnsupportedOperationException("CVC4 doesn't support comparision between 2 cardinality expressions.");
        }

        if
        (
                (expr.left instanceof ExprUnary &&
                        ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY &&
                        (!(expr.right instanceof ExprConstant &&
                                ((ExprConstant) expr.right).op == ExprConstant.Op.NUMBER))) ||
                        (expr.right instanceof ExprUnary &&
                                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY &&
                                (!(expr.left instanceof ExprConstant &&
                                        ((ExprConstant) expr.left).op == ExprConstant.Op.NUMBER)))
        )
        {
            throw new UnsupportedOperationException("CVC4 only supports cardinality with constant numbers");
        }


        // translate cardinality differently
        if
        ((expr.left instanceof ExprUnary &&
                ((ExprUnary) expr.left).op == ExprUnary.Op.CARDINALITY)
        )
        {
            int n = ((ExprConstant) expr.right).num;
            Expression equality = translateEqCardComparison((ExprUnary) expr.left, n, op, environment);
            return equality;
        }

        if
        ((expr.right instanceof ExprUnary &&
                ((ExprUnary) expr.right).op == ExprUnary.Op.CARDINALITY)
        )
        {
            int n = ((ExprConstant) expr.left).num;
            Expression equality = translateEqCardComparison((ExprUnary) expr.right, n, op, environment);
            return equality;
        }

        throw new UnsupportedOperationException();
    }

    private Expression translateEqCardComparison(ExprUnary expr, int n, BinaryExpression.Op op, Environment environment)
    {
        Environment newEnvironment = new Environment(environment);
        Expression expression = exprTranslator.translateExpr(expr.sub, newEnvironment);
        if (n == 0)
        {
            // the set expression is empty
            Expression empty = UnaryExpression.Op.EMPTYSET.make(expression.getSort());
            Expression equal = BinaryExpression.Op.EQ.make(expression, empty);
            Expression finalExpression = exprTranslator.translateAuxiliaryFormula(equal, newEnvironment);
            return finalExpression;
        }

        List<Expression> variables = new ArrayList<>();
        List<VariableDeclaration> declarations = new ArrayList<>();

        Sort sort = ((SetSort) expression.getSort()).elementSort;
        for(int i = 0; i < n; i++)
        {
            VariableDeclaration variable = new VariableDeclaration(TranslatorUtils.getFreshName(sort), sort, false);
            declarations.add(variable);
        }

        for (VariableDeclaration declaration : declarations)
        {
            variables.add(declaration.getVariable());
        }

        Expression distinct;

        if (variables.size() == 1)
        {
            // distinct operator needs at least 2 arguments
            distinct = BoolConstant.True;
        }
        else
        {
            distinct = MultiArityExpression.Op.DISTINCT.make(variables);
        }

        Expression set = TranslatorUtils.makeRelation(variables);
        Expression equal = BinaryExpression.Op.EQ.make(expression, set);
        Expression and = MultiArityExpression.Op.AND.make(equal, distinct);
        Expression exists = QuantifiedExpression.Op.EXISTS.make(and, declarations);

        Expression finalExpression = exprTranslator.translateAuxiliaryFormula(exists, newEnvironment);

        switch (op)
        {
            case EQ:
            {
                return  finalExpression;
            }
            default:
                throw new UnsupportedOperationException();
        }
    }

    private Expression translateSetOperation(ExprBinary expr, BinaryExpression.Op op, Environment environment)
    {
        Expression left = exprTranslator.translateExpr(expr.left, environment);
        Expression right = exprTranslator.translateExpr(expr.right, environment);

        if (left instanceof Variable &&
                (!(((Variable) left).getDeclaration().getSort() instanceof SetSort)))
        {
            left = TranslatorUtils.makeRelation((Variable) left);
        }
        else if (left instanceof MultiArityExpression &&
                ((MultiArityExpression) left).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            left = AlloyUtils.mkSingletonOutOfTuple((MultiArityExpression) left);
        }
        if (right instanceof Variable &&
                (!(((Variable) right).getDeclaration().getSort() instanceof SetSort)))
        {
            right = TranslatorUtils.makeRelation((Variable) right);
        }
        else if (right instanceof MultiArityExpression &&
                ((MultiArityExpression) right).getOp() == MultiArityExpression.Op.MKTUPLE)
        {
            right = AlloyUtils.mkSingletonOutOfTuple((MultiArityExpression) right);
        }

        BinaryExpression operation = op.make(left, right);
        return operation;
    }

    private Expression translateSubsetOperation(ExprBinary expr, Environment environment)
    {
        Environment environmentA = new Environment(environment);
        Expression A = exprTranslator.translateExpr(expr.left, environmentA);
        A = exprTranslator.translator.handleIntConstant(A);

        Environment environmentB = new Environment(environment);
        Expression B = exprTranslator.translateExpr(expr.right, environmentB);
        B = exprTranslator.translator.handleIntConstant(B);

        // left sort | right sort | Translation
        // -------------------------------------
        // tuple     | tuple      | (= A B)
        // tuple     | set        | (member tuple set)
        // set       | set        | (subset A B)
        Expression translation;
        if (A.getSort() instanceof TupleSort && B.getSort() instanceof TupleSort)
        {
            translation = BinaryExpression.Op.EQ.make(A, B);
        }
        else if (A.getSort() instanceof TupleSort && B.getSort() instanceof SetSort)
        {
            translation = BinaryExpression.Op.MEMBER.make(A, B);
        }
        else
        {
            translation = BinaryExpression.Op.SUBSET.make(A, B);
        }

        translation = exprTranslator.translateAuxiliaryFormula(translation, environmentA);

        if (environmentB.getAuxiliaryFormula() == null)
        {
            return translation;
        }
        assert environmentB.getAuxiliaryFormula().getOp() == QuantifiedExpression.Op.EXISTS;
        Expression expression = environmentB.getAuxiliaryFormula();
        expression = ((QuantifiedExpression) expression).getExpression().replace(B, A);
        return expression;
    }

    private Expression translateJoin(ExprBinary expr, Environment environment)
    {
        Expression A = exprTranslator.translateExpr(expr.left, environment);
        Expression B = exprTranslator.translateExpr(expr.right, environment);
        A = TranslatorUtils.makeRelation(A);
        B = TranslatorUtils.makeRelation(B);
        BinaryExpression join = BinaryExpression.Op.JOIN.make(A, B);
        return join;
    }
}
