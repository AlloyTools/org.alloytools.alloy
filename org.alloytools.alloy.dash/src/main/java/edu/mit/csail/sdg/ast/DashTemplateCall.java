package edu.mit.csail.sdg.ast;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTemplateCall {

    Pos                 pos;
    public String       name          = "";
    public String       templateName  = "";
    public List<String> templateParam = new ArrayList<String>();

    public DashTemplateCall(Pos pos, String name, String templateName, List<ExprVar> templateParam) {
        this.pos = pos;
        this.name = name;
        this.templateName = templateName;

        for (ExprVar var : templateParam) {
            this.templateParam.add(var.toString());
        }
    }
}
