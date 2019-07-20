package edu.uiowa.alloy2smt.translators;

import edu.mit.csail.sdg.ast.*;
import edu.uiowa.alloy2smt.utils.AlloyUtils;
import edu.uiowa.smt.TranslatorUtils;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class AlloyUtilsTests
{
    @BeforeEach
    public void reset()
    {
        TranslatorUtils.reset();
    }


    @Test
    public void substitute1()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        Expr intersect = ExprBinary.Op.INTERSECT.make(null, null, x, x);
        ExprVar y = ExprVar.make(null, "y", A.type());
        Expr newExpr = AlloyUtils.substituteExpr(intersect, x, y);
        assertEquals("x & x", intersect.toString());
        assertEquals("y & y", newExpr.toString());
    }

    @Test
    public void substitute2()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        ExprVar y = ExprVar.make(null, "y", A.type());
        Expr newExpr = AlloyUtils.substituteExpr(no, x, y);
        assertEquals("no x", no.toString());
        assertEquals("no y", newExpr.toString());
    }

    @Test
    public void substitute3()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(x), A);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        ExprVar y = ExprVar.make(null, "y", A.type());
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, y);
        assertEquals("(all x | no x)", exprQt.toString());
        assertEquals("(all x | no x)", newExpr.toString());
    }

    @Test
    public void substitute4()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(y), A);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, y);
        assertEquals("(all y | no x)", exprQt.toString());
        assertEquals("(all x.1 | no y)", newExpr.toString());
    }

    @Test
    public void substitute5()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        Expr product = ExprBinary.Op.ARROW.make(null, null, y, y);
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(y), A);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, product);
        assertEquals("(all y | no x)", exprQt.toString());
        assertEquals("(all x.1 | no y -> y)", newExpr.toString());
    }

    @Test
    public void substitute6()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        ExprVar z = ExprVar.make(null, "z", A.type());
        ExprVar w = ExprVar.make(null, "w", A.type());
        Expr xInA = ExprBinary.Op.IN.make(null, null, x, A);

        Expr zAndY = ExprBinary.Op.INTERSECT.make(null, null, z, y);
        Expr noZAndY = ExprUnary.Op.NO.make(null, zAndY);
        Decl decl = new Decl(null, null, null, Collections.singletonList(x), A);
        Expr comprehension = ExprQt.Op.COMPREHENSION.make(null, null, Collections.singletonList(decl), xInA);
        Expr let = ExprLet.make(null, z, comprehension, noZAndY);
        Expr newExpr = AlloyUtils.substituteExpr(let, y, w);
        assertEquals("(let z= {x | x in A} | no z & y)", let.toString());
        assertEquals("no {x | x in A} & w", newExpr.toString());
    }

    @Test
    public void substitute7()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        ExprVar z = ExprVar.make(null, "z", A.type());
        Expr xInA = ExprBinary.Op.IN.make(null, null, x, A);

        Expr zAndY = ExprBinary.Op.INTERSECT.make(null, null, z, y);
        Expr noZAndY = ExprUnary.Op.NO.make(null, zAndY);
        Decl decl = new Decl(null, null, null, Collections.singletonList(x), A);
        Expr comprehension = ExprQt.Op.COMPREHENSION.make(null, null, Collections.singletonList(decl), xInA);
        Expr let = ExprLet.make(null, z, comprehension, noZAndY);
        Expr newExpr = AlloyUtils.substituteExpr(let, y, z);
        assertEquals("(let z= {x | x in A} | no z & y)", let.toString());
        assertEquals("no {x | x in A} & z", newExpr.toString());
    }

    @Test
    public void substitute8()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        ExprVar z = ExprVar.make(null, "z", A.type());
        Expr zAndY = ExprBinary.Op.INTERSECT.make(null, null, z, y);
        Expr let = ExprLet.make(null, z, y, zAndY);
        Expr newExpr = AlloyUtils.substituteExpr(let, y, z);
        assertEquals("(let z= y | z & y)", let.toString());
        assertEquals("z & z", newExpr.toString());
    }

    @Test
    public void substitute9()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        Expr none = ExprConstant.EMPTYNESS;
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());

        Expr equal = ExprBinary.Op.EQUALS.make(null, null, x, none);

        Expr newExpr = AlloyUtils.substituteExpr(equal, x, y);
        assertEquals("x = none", equal.toString());
        assertEquals("y = none", newExpr.toString());
    }

    @Test
    public void substitute10()
    {
        Sig A = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", A.type());
        ExprVar y = ExprVar.make(null, "y", A.type());
        ExprVar z = ExprVar.make(null, "z", A.type());

        Expr xInY = ExprBinary.Op.IN.make(null, null, x, y);
        Expr ite = ExprITE.make(null, xInY, x, y);

        Expr newExpr = AlloyUtils.substituteExpr(ite, y, z);
        assertEquals("(x in y => x else y)", ite.toString());
        assertEquals("(x in z => x else z)", newExpr.toString());
    }
}
