package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

/* Stores information regarding a transition within a state/concState */
public class Trans {

    public Expr          doExpr        = null;
    public Expr          whenExpr      = null;

    public List<String>  fromExpr      = new ArrayList<String>();
    public String        onExpr        = null;
    public List<String>  gotoExpr      = new ArrayList<String>();
    public String        sendExpr      = null;
    public List<ExprVar> templateParam = new ArrayList<ExprVar>();
    public String        templateName  = null;

    public String        name          = "";
    public Object        parentState;
    public String        modifiedName  = "";
    public Pos           pos;

    public Pos           doExprPos     = null;
    public Pos           whenExprPos   = null;

    public Pos           fromExprPos   = null;
    public Pos           onExprPos     = null;
    public Pos           gotoExprPos   = null;
    public Pos           sendExprPos   = null;
    public Pos           templatePos   = null;

    /*
     * This is used to create a transition that only has a call to a transition
     * template
     */
    public Trans(Pos pos, String name, Object templateCall) {
        this.name = name;
        this.pos = pos;
        if (templateCall instanceof DashExpr) {
            DashExpr transItem = (DashExpr) templateCall;
            this.templateName = transItem.name;
            this.templateParam = transItem.templateParam;
        }
    }


    /*
     * TransItems is the list of items that is inside a transition. An example of an
     * items is do statement, goto statement, etc.
     */
    public Trans(Pos pos, String name, List<Object> transItems) {
        this.name = name;
        this.pos = pos;

        for (Object item : transItems) {
            if (item instanceof DashExpr) {
                DashExpr transItem = ((DashExpr) item);
                String itemName = ((DashExpr) item).type;
                switch (itemName) {
                    case "from" :
                        if (transItem.names != null) {
                            if (transItem.names.size() > 0) {
                                for (ExprVar var : transItem.names) {
                                    this.fromExpr.add(var.toString());
                                }
                                this.fromExprPos = transItem.pos;
                            }
                        }
                        break;
                    case "on" :
                        this.onExpr = transItem.name;
                        this.onExprPos = transItem.pos;
                        break;
                    case "when" :
                        this.whenExpr = transItem.expr;
                        this.whenExprPos = transItem.pos;
                        break;
                    case "do" :
                        this.doExpr = transItem.expr;
                        this.doExprPos = transItem.pos;
                        break;
                    case "goto" :
                        if (transItem.names != null) {
                            if (transItem.names.size() > 0) {
                                System.out.println("Adding: " + transItem.names);
                                for (ExprVar var : transItem.names)
                                    this.gotoExpr.add(var.toString());
                                this.gotoExprPos = transItem.pos;
                            }
                        }
                        break;
                    case "send" :
                        this.sendExpr = transItem.name;
                        this.sendExprPos = transItem.pos;
                        break;
                    case "template" :
                        this.templateName = transItem.name;
                        this.templateParam = transItem.templateParam;
                        break;
                }
            }
        }
    }
}


