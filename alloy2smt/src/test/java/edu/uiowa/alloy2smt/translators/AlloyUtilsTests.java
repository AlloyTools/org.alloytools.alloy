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
        Sig sig = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", sig.type());
        Expr intersect = ExprBinary.Op.INTERSECT.make(null, null, x, x);
        ExprVar y = ExprVar.make(null, "y", sig.type());
        Expr newIntersect = AlloyUtils.substituteExpr(intersect, x, y);
        assertEquals("y & y", newIntersect.toString());
    }

    @Test
    public void substitute2()
    {
        Sig sig = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", sig.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        ExprVar y = ExprVar.make(null, "y", sig.type());
        Expr newExpr = AlloyUtils.substituteExpr(no, x, y);
        assertEquals("no y", newExpr.toString());
    }

    @Test
    public void substitute3()
    {
        Sig sig = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", sig.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(x), sig);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        ExprVar y = ExprVar.make(null, "y", sig.type());
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, y);
        assertEquals("(all x | no x)", newExpr.toString());
    }

    @Test
    public void substitute4()
    {
        Sig sig = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", sig.type());
        ExprVar y = ExprVar.make(null, "y", sig.type());
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(y), sig);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, y);
        assertEquals("(all y | no x)", exprQt.toString());
        assertEquals("(all _a1 | no y)", newExpr.toString());
    }

    @Test
    public void substitute5()
    {
        Sig sig = new Sig.PrimSig("A", Sig.UNIV);
        ExprVar x = ExprVar.make(null, "x", sig.type());
        ExprVar y = ExprVar.make(null, "y", sig.type());
        Expr product = ExprBinary.Op.ARROW.make(null, null, y, y);
        Expr no = ExprUnary.Op.NO.make(null, x);
        Decl decl = new Decl(null, null, null, Collections.singletonList(y), sig);
        Expr exprQt = ExprQt.Op.ALL.make(null, null, Collections.singletonList(decl), no);
        Expr newExpr = AlloyUtils.substituteExpr(exprQt, x, product);
        assertEquals("(all y | no x)", exprQt.toString());
        assertEquals("(all _a1 | no y -> y)", newExpr.toString());
    }
}
