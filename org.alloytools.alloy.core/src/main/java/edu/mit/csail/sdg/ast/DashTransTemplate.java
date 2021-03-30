package edu.mit.csail.sdg.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTransTemplate {

    public Pos           pos;
    public String        name     = "";
    public List<Decl>    decls;

    public DashFrom      fromExpr = null;
    public DashOn        onExpr   = null;
    public DashWhenExpr  whenExpr = null;
    public DashDoExpr    doExpr   = null;
    public DashGoto      gotoExpr = null;
    public DashSend      sendExpr = null;

    public DashConcState parent   = null;

    public DashTransTemplate(Pos pos, String name, List<Object> stateItems, List<Decl> decls) {
        this.pos = pos;
        this.name = name;
        this.decls = decls;

        for (Object item : stateItems) {
            if (item instanceof DashFrom)
                fromExpr = (DashFrom) item;
            if (item instanceof DashOn)
                onExpr = (DashOn) item;
            if (item instanceof DashWhenExpr)
                whenExpr = (DashWhenExpr) item;
            if (item instanceof DashDoExpr)
                doExpr = (DashDoExpr) item;
            if (item instanceof DashGoto)
                gotoExpr = (DashGoto) item;
            if (item instanceof DashSend)
                sendExpr = (DashSend) item;
        }
    }
}
