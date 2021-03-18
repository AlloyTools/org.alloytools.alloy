package edu.mit.csail.sdg.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

/* Stores information regarding a transition within a state/concState */
public class Trans {

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
    public Trans(Pos pos, String name, List<Object> transItems) {
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
            if (item instanceof DashTransTemplate)
                transTemplate = (DashTransTemplate) item;

        }
    }
}


