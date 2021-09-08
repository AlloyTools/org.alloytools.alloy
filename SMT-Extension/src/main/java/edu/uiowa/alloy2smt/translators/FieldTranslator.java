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
import edu.uiowa.smt.SmtEnv;
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
    if (fields.size() == 0)
    {
      return;
    }

    // translate disjoint fields
    for (Decl decl : sig.getFieldDecls())
    {
      // disjoint fields
      if (decl.disjoint != null && decl.names.size() > 1)
      {
        for (int i = 0; i < decl.names.size() - 1; i++)
        {
          SmtExpr fieldI = getFieldExpression(fields, decl.names.get(i).label);
          for (int j = i + 1; j < decl.names.size(); j++)
          {
            SmtExpr fieldJ = getFieldExpression(fields, decl.names.get(j).label);
            SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(fieldI, fieldJ);
            SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(fieldI.getSort());
            SmtExpr equal = SmtBinaryExpr.Op.EQ.make(intersect, emptySet);
            List<Pos> positions = Arrays.asList(decl.names.get(i).pos, decl.names.get(j).pos);
            Assertion disjoint = AlloyUtils.getAssertion(positions,
                String.format("disj %1$s, %2$s", decl.names.get(i), decl.names.get(j)), equal);
            translator.smtScript.addAssertion(disjoint);
          }
        }
      }
    }
  }

  private void translateDisjoint2FieldValues(Sig sig, List<Sig.Field> fields)
  {
    if (fields.size() == 0)
    {
      return;
    }

    // translate disjoint field values

    // sig S {f: disj e}
    // all a, b: S | a != b implies no a.f & b.f

    SmtExpr signature = translator.signaturesMap.get(sig).getVariable();
    SetSort setSort = (SetSort) signature.getSort();
    SmtVariable a = new SmtVariable("a", setSort.elementSort, false);
    SmtVariable b = new SmtVariable("b", setSort.elementSort, false);
    SmtExpr aMember = SmtBinaryExpr.Op.MEMBER.make(a.getVariable(), signature);
    SmtExpr bMember = SmtBinaryExpr.Op.MEMBER.make(b.getVariable(), signature);
    SmtExpr aSingleton = SmtUnaryExpr.Op.SINGLETON.make(a.getVariable());
    SmtExpr bSingleton = SmtUnaryExpr.Op.SINGLETON.make(b.getVariable());

    SmtExpr members = SmtMultiArityExpr.Op.AND.make(aMember, bMember);
    SmtExpr equal = SmtBinaryExpr.Op.EQ.make(a.getVariable(), b.getVariable());
    SmtExpr notEqual = SmtUnaryExpr.Op.NOT.make(equal);
    SmtExpr antecedent = SmtMultiArityExpr.Op.AND.make(members, notEqual);
    SmtExpr consequent = BoolConstant.True;

    //ToDo: refactor for unsat core
    List<Pos> positions = new ArrayList<>();
    for (Decl decl : sig.getFieldDecls())
    {
      if (decl.disjoint2 != null)
      {
        for (ExprHasName name : decl.names)
        {
          SmtExpr field = getFieldExpression(fields, name.label);
          SmtExpr aJoin = SmtBinaryExpr.Op.JOIN.make(aSingleton, field);
          SmtExpr bJoin = SmtBinaryExpr.Op.JOIN.make(bSingleton, field);
          SmtExpr intersect = SmtBinaryExpr.Op.INTERSECTION.make(aJoin, bJoin);
          SmtExpr emptySet = SmtUnaryExpr.Op.EMPTYSET.make(intersect.getSort());
          SmtExpr isEmpty = SmtBinaryExpr.Op.EQ.make(intersect, emptySet);
          consequent = SmtMultiArityExpr.Op.AND.make(consequent, isEmpty);
          positions.add(name.pos);
        }
      }
    }

    if (!consequent.equals(BoolConstant.True))
    {
      SmtExpr implies = SmtBinaryExpr.Op.IMPLIES.make(antecedent, consequent);
      SmtExpr forAll = SmtQtExpr.Op.FORALL.make(implies, a, b);

      Assertion disjoint2 = AlloyUtils.getAssertion(positions, sig.label + " disjoint2", forAll);
      translator.smtScript.addAssertion(disjoint2);
    }
  }

  private SmtExpr getFieldExpression(List<Sig.Field> fields, String label)
  {
    Optional<Sig.Field> field = fields.stream()
                                      .filter(f -> f.label.equals(label))
                                      .findFirst();
    if (!field.isPresent())
    {
      throw new RuntimeException("Can not find field " + label);
    }
    SmtExpr smtExpr = translator.fieldsMap.get(field.get()).getVariable();
    return smtExpr;
  }

  void translate(Sig.Field field)
  {

    String fieldName = field.sig.label + "/" + field.label;

    if (fieldName.equals("integer/univInt/idenInt"))
    {
      translator.fieldsMap.put(field, AbstractTranslator.idenInt);
      return;
    }

    List<Sort> fieldSorts = new ArrayList<>();

    for (Sig sig : field.type().fold().get(0))
    {
      if (sig.type().is_int())
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
    translator.smtScript.addFunction(fieldDeclaration);
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
    Expr exprLet = ExprLet.make(null, s, zisJoinField, in);

    Expr oneOfSig = ExprUnary.Op.ONEOF.make(null, field.sig);
    Decl decl = new Decl(null, null, null, null, Collections.singletonList(zis), oneOfSig);
    Expr all = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), exprLet);

    SmtEnv smtEnv = new SmtEnv();
    SmtExpr multiplicity = translator.exprTranslator.translateExpr(all, smtEnv);
    Assertion assertion = AlloyUtils.getAssertion(Collections.singletonList(field.pos), field.toString() + " multiplicity", multiplicity);
    translator.smtScript.addAssertion(assertion);

    Expr noMultiplicity = AlloyUtils.removeMultiplicity(field.decl());
    Expr substituteExpr = AlloyUtils.substituteExpr(noMultiplicity, zis, field.sig);

    Expr product = ExprBinary.Op.ARROW.make(null, null, field.sig, substituteExpr);
    Expr subsetExpr = ExprBinary.Op.IN.make(null, null, field, product);
    translator.exprTranslator.translateFormula(field.toString() + " subset", subsetExpr);
  }
}
