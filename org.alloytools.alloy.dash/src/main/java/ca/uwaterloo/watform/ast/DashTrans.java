package ca.uwaterloo.watform.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

/* Stores information regarding a transition within a state/concState */
public class DashTrans {

    public DashFrom          fromExpr      = null;
    public DashOn            onExpr        = null;
    public DashWhenExpr      whenExpr      = null;
    public DashDoExpr        doExpr        = null;
    public DashGoto          gotoExpr      = null;
    public DashSend          sendExpr      = null;
    public DashTransTemplate transTemplate = null;

    public String            name          = "";
    public Object            parentState;
    public String            modifiedName  = "";
    public Pos               pos;


    /*
     * TransItems is the list of items that is inside a transition. An example of an
     * items is do statement, goto statement, etc.
     */
    public DashTrans(Pos pos, String name, List<Object> transItems) {
        this.name = name;
        this.pos = pos;

        for (Object item : transItems) {
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


    public DashTrans(DashTrans trans) {
        this.fromExpr = trans.fromExpr;
        this.onExpr = trans.onExpr;
        this.whenExpr = trans.whenExpr;
        this.doExpr = trans.doExpr;
        this.gotoExpr = trans.gotoExpr;
        this.sendExpr = trans.sendExpr;

        this.name = trans.name;
        this.modifiedName = trans.modifiedName;
        this.parentState = trans.parentState;
        this.pos = null;
    }
}
