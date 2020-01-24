/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 *
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.AbstractTranslator;
import edu.uiowa.smt.Environment;
import edu.uiowa.smt.smtAst.*;

import java.util.*;

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
        if(fields.size() == 0)
        {
            return;
        }

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
                        List<Pos> positions = Arrays.asList(decl.names.get(i).pos, decl.names.get(j).pos);
                        Assertion disjoint = AlloyUtils.getAssertion(positions,
                                String.format("disj %1$s, %2$s", decl.names.get(i), decl.names.get(j)), equal);
                        translator.smtProgram.addAssertion(disjoint);
                    }
                }
            }
        }
    }

    private void translateDisjoint2FieldValues(Sig sig, List<Sig.Field> fields)
    {
        if(fields.size() == 0)
        {
            return;
        }

        // translate disjoint field values

        // sig S {f: disj e}
        // all a, b: S | a != b implies no a.f & b.f

        Expression signature = translator.signaturesMap.get(sig).getVariable();
        SetSort setSort = (SetSort) signature.getSort();
        VariableDeclaration a = new VariableDeclaration("a", setSort.elementSort, false);
        VariableDeclaration b = new VariableDeclaration("b", setSort.elementSort, false);
        Expression aMember = BinaryExpression.Op.MEMBER.make(a.getVariable(), signature);
        Expression bMember = BinaryExpression.Op.MEMBER.make(b.getVariable(), signature);
        Expression aSingleton = UnaryExpression.Op.SINGLETON.make(a.getVariable());
        Expression bSingleton = UnaryExpression.Op.SINGLETON.make(b.getVariable());

        Expression members = MultiArityExpression.Op.AND.make(aMember, bMember);
        Expression equal = BinaryExpression.Op.EQ.make(a.getVariable(), b.getVariable());
        Expression notEqual = UnaryExpression.Op.NOT.make(equal);
        Expression antecedent = MultiArityExpression.Op.AND.make(members, notEqual);
        Expression consequent = BoolConstant.True;

        //ToDo: refactor for unsat core
        List<Pos> positions = new ArrayList<>();
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
                    consequent = MultiArityExpression.Op.AND.make(consequent, isEmpty);
                    positions.add(name.pos);
                }
            }
        }

        if(! consequent.equals(BoolConstant.True))
        {
            Expression implies = BinaryExpression.Op.IMPLIES.make(antecedent, consequent);
            Expression forAll = QuantifiedExpression.Op.FORALL.make(implies, a, b);

            Assertion disjoint2 = AlloyUtils.getAssertion(positions, sig.label + " disjoint2", forAll);
            translator.smtProgram.addAssertion(disjoint2);
        }
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

        if(fieldName.equals("integer/univInt/idenInt"))
        {
            translator.fieldsMap.put(field, AbstractTranslator.idenInt);
            return;
        }

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

        Sort sort = new SetSort(new TupleSort(fieldSorts));
        FunctionDeclaration fieldDeclaration = new FunctionDeclaration(fieldName, sort, true);
        // declare a variable for the field
        translator.smtProgram.addFunction(fieldDeclaration);
        translator.fieldsMap.put(field, fieldDeclaration);
        translateMultiplicities(field);
    }

    private void translateMultiplicities(Sig.Field field)
    {
        Expr expr = field.decl().expr;
        // Sig A {field: expr}
        // all this: A | let $s$ = this.field | $s$ in expr
        // field in (A -> removeMultiplicity[expr]) because A is not a type in SMT
        ExprVar zis = ExprVar.make(null, "this", field.sig.type());
        Expr zisJoinField = ExprBinary.Op.JOIN.make(null, null, zis, field);
        ExprVar s = ExprVar.make(null, "$s$", zisJoinField.type());
        Expr in = ExprBinary.Op.IN.make(null, null, s, expr);
        Expr exprLet = ExprLet.make(null, s, zisJoinField , in);

        Expr oneOfSig = ExprUnary.Op.ONEOF.make(null, field.sig);
        Decl decl = new Decl(null, null, null, Collections.singletonList(zis), oneOfSig);
        Expr all = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), exprLet);

        Expression multiplicity =  translator.exprTranslator.translateExpr(all, new Environment());
        Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(field.pos),field.toString() + " multiplicity", multiplicity);
        translator.smtProgram.addAssertion(assertion);

        Expr noMultiplicity = AlloyUtils.removeMultiplicity(field.decl());
        Expr substituteExpr = AlloyUtils.substituteExpr(noMultiplicity, zis, field.sig);

        Expr product = ExprBinary.Op.ARROW.make(null, null, field.sig, substituteExpr);
        Expr subsetExpr = ExprBinary.Op.IN.make(null, null, field, product);
        translator.exprTranslator.translateFormula(field.toString() + " subset", subsetExpr);
    }
}
