package edu.mit.csail.sdg.ast;

import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTemplateCall {

    Pos           pos;
    String        templateName;
    List<ExprVar> templateParam;

    public DashTemplateCall(Pos pos, String templateName, List<ExprVar> templateParam) {
        this.pos = pos;
        this.templateName = templateName;
        this.templateParam = templateParam;
    }
}
