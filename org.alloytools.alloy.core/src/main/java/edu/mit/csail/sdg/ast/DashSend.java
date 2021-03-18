package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashSend {

    Pos    pos;
    String sendExpr;

    public DashSend(Pos pos, String sendExpr) {
        this.pos = pos;
        this.sendExpr = sendExpr;
    }
}
