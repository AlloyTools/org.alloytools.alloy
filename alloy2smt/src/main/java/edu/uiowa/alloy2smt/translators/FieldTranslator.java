/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.TranslatorUtils;
import edu.uiowa.smt.smtAst.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class FieldTranslator
{

    private final Alloy2SmtTranslator translator;

    public FieldTranslator(Alloy2SmtTranslator translator)
    {
        this.translator = translator;
    }

    void translateFields()
    {
        for (Sig sig : translator.reachableSigs)
        {
            List<Sig.Field> fields = sig.getFields().makeCopy();
            for (Sig.Field f : fields)
            {
                translate(f);
            }

            translateDisjointFields(sig, fields);

            translateDisjoint2FieldValues(sig, fields);
        }
    }

    private void translateDisjointFields(Sig sig, List<Sig.Field> fields)
    {
        // translate disjoint fields
        for (Decl decl: sig.getFieldDecls())
        {
            // disjoint fields
            if (decl.disjoint != null && decl.names.size() > 1)
            {
                for (int i = 0; i < decl.names.size() - 1; i++)
                {
                    Expression fieldI = getFieldExpression(fields, decl.names.get(i).label);
                    for (int j = i + 1; j < decl.names.size(); j++)
                    {
                        Expression fieldJ = getFieldExpression(fields, decl.names.get(j).label);
                        Expression intersect = BinaryExpression.Op.INTERSECTION.make(fieldI, fieldJ);
                        Expression emptySet = UnaryExpression.Op.EMPTYSET.make(fieldI.getSort());
                        Expression equal = BinaryExpression.Op.EQ.make(intersect, emptySet);
                        Assertion disjoint = new Assertion(String.format("disj %1$s, %2$s", decl.names.get(i), decl.names.get(j)), equal);
                        translator.smtProgram.addAssertion(disjoint);
                    }
                }
            }
        }
    }

    private void translateDisjoint2FieldValues(Sig sig, List<Sig.Field> fields)
    {
        // translate disjoint field values

        // sig S {f: disj e}
        // all a, b: S | a != b implies no a.f & b.f

        Expression signature = translator.signaturesMap.get(sig).getVariable();
        SetSort setSort = (SetSort) signature.getSort();
        VariableDeclaration a = new VariableDeclaration("__a__", setSort.elementSort, null);
        VariableDeclaration b = new VariableDeclaration("__b__", setSort.elementSort, null);
        Expression aMember = BinaryExpression.Op.MEMBER.make(a.getVariable(), signature);
        Expression bMember = BinaryExpression.Op.MEMBER.make(b.getVariable(), signature);
        Expression aSingleton = UnaryExpression.Op.SINGLETON.make(a.getVariable());
        Expression bSingleton = UnaryExpression.Op.SINGLETON.make(b.getVariable());

        Expression members = BinaryExpression.Op.AND.make(aMember, bMember);
        Expression equal = BinaryExpression.Op.EQ.make(a.getVariable(), b.getVariable());
        Expression notEqual = UnaryExpression.Op.NOT.make(equal);
        Expression antecedent = BinaryExpression.Op.AND.make(members, notEqual);
        Expression consequent = BoolConstant.True;

        for (Decl decl: sig.getFieldDecls())
        {
            if (decl.disjoint2 != null)
            {
                for (ExprHasName name: decl.names)
                {
                    Expression field = getFieldExpression(fields, name.label);
                    Expression aJoin = BinaryExpression.Op.JOIN.make(aSingleton, field);
                    Expression bJoin = BinaryExpression.Op.JOIN.make(bSingleton, field);
                    Expression intersect = BinaryExpression.Op.INTERSECTION.make(aJoin, bJoin);
                    Expression emptySet = UnaryExpression.Op.EMPTYSET.make(intersect.getSort());
                    Expression isEmpty = BinaryExpression.Op.EQ.make(intersect, emptySet);
                    consequent = BinaryExpression.Op.AND.make(consequent, isEmpty);
                }
            }
        }

        Expression implies = BinaryExpression.Op.IMPLIES.make(antecedent, consequent);
        Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, a, b);

        Assertion disjoint2 = new Assertion(sig.label + " disjoint2", forAll);
        translator.smtProgram.addAssertion(disjoint2);
    }

    private Expression getFieldExpression(List<Sig.Field> fields, String label)
    {
        Optional<Sig.Field> field =  fields.stream()
            .filter(f -> f.label.equals(label))
            .findFirst();
        if(!field.isPresent())
        {
            throw new RuntimeException("Can not find field " + label);
        }
        Expression expression = translator.fieldsMap.get(field.get()).getVariable();
        return expression;
    }

    void translate(Sig.Field field)
    {

        String      fieldName   = field.sig.label + "/" + field.label;
        List<Sort>  fieldSorts  = new ArrayList<>();

        for (Sig sig : field.type().fold().get(0))
        {
            if(sig.type().is_int())
            {
                fieldSorts.add(AbstractTranslator.uninterpretedInt);
            }
            else
            {
                fieldSorts.add(AbstractTranslator.atomSort);
            }
        }

        FunctionDeclaration fieldDeclaration = new FunctionDeclaration(fieldName, new SetSort(new TupleSort(fieldSorts)));
        // declare a variable for the field
        translator.smtProgram.addFunction(fieldDeclaration);
        translator.fieldsMap.put(field, fieldDeclaration);
        translateMultiplicities(field);
    }

    private void translateMultiplicities(Sig.Field field)
    {
        Expr expr = field.decl().expr;
        if(expr instanceof ExprUnary)
        {
            ExprUnary exprUnary = (ExprUnary) expr;
            Expr A = field.sig;
            Expr B = exprUnary.sub;

            Expr multiplicity;
            switch (exprUnary.op)
            {
                case SOMEOF:
                {
                    multiplicity = ExprBinary.Op.ANY_ARROW_SOME.make(null, null, A, B);
                }break;
                case ONEOF:
                {
                    multiplicity = ExprBinary.Op.ANY_ARROW_ONE.make(null, null, A, B);
                }break;
                case LONEOF:
                {
                    multiplicity = ExprBinary.Op.ANY_ARROW_LONE.make(null, null, A, B);
                }break;
                case SETOF:
                {
                    multiplicity = ExprBinary.Op.ARROW.make(null, null, A, B);
                }break;
                default:
                    throw new UnsupportedOperationException();
            }
            Expression set = translator.exprTranslator.translateExpr(multiplicity);
            FunctionDeclaration fieldFunction =  translator.fieldsMap.get(field);
            Expression constraint;
            if(exprUnary.op == ExprUnary.Op.SETOF)
            {
                constraint = BinaryExpression.Op.SUBSET.make(fieldFunction.getVariable(), set);
            }
            else
            {
                constraint = BinaryExpression.Op.EQ.make(fieldFunction.getVariable(), set);
            }
            translator.smtProgram.addAssertion(new Assertion(field.toString() + " multiplicity", constraint));
        }
        else
        {
            // sig A {field : expr}
            // Set is a subset of expr
            // all z: A | z.field in Set
            // and A.field = Set
            // and A x field in A x Set

            ExprVar z = ExprVar.make(null, "__z__", field.sig.type());
            Expr noopZ = ExprUnary.Op.NOOP.make(null, z);
            Expr noopField = ExprUnary.Op.NOOP.make(null, field);
            Expr join = ExprBinary.Op.JOIN.make(null, null, noopZ, noopField);
            Expr in = ExprBinary.Op.IN.make(null, null, join, expr);
            Expr noopSig = ExprUnary.Op.NOOP.make(null, field.sig);
            Decl decl = new Decl(null, null, null, Collections.singletonList(z), noopSig);
            Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), in);
            Expression multiplicity =  translator.exprTranslator.translateExpr(exprQt);
            translator.smtProgram.addAssertion(new Assertion(field.toString() + " multiplicity", multiplicity));
            Expr product = ExprBinary.Op.ARROW.make(null, null, noopSig, expr);
            Expr subsetExpr = ExprBinary.Op.IN.make(null, null, noopField, product);
            Expression subsetExpression = translator.exprTranslator.translateExpr(subsetExpr);
            translator.smtProgram.addAssertion(new Assertion(field.toString() + " subset", subsetExpression));

            // no set is generated for AnyArrowAny constraint
            if(translator.multiplicityVariableMap.containsKey(expr))
            {
                Expr joinSigField = ExprBinary.Op.JOIN.make(null, null, noopSig, noopField);
                Expression joinExpression = translator.exprTranslator.translateExpr(joinSigField);
                Expression set = translator.multiplicityVariableMap.get(expr).getVariable();
                Expression equality = BinaryExpression.Op.EQ.make(joinExpression, set);
                translator.smtProgram.addAssertion(new Assertion(field.toString() + " auxiliary set", equality));
                translator.multiplicityVariableMap.remove(expr);
            }
        }
    }
}
