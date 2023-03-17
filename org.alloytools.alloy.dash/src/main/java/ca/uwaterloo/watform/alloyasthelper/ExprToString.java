package ca.uwaterloo.watform.alloyasthelper;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.StringJoiner;

import com.io7m.jpplib.core.Layouter;
import com.io7m.jpplib.core.Backend;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

import ca.uwaterloo.watform.core.DashErrors;

public class ExprToString {

    int indent;
    int lineWidth;
    Layouter<NoExceptions> out;
    Boolean isAfterAlloyResolveAll;
    
    public ExprToString(boolean isAfterAlloyResolveAll) {
        this.isAfterAlloyResolveAll = isAfterAlloyResolveAll;
        this.indent = 4;
        this.lineWidth = 120;
        Backend back = new Backend(lineWidth);
        this.out = new Layouter<NoExceptions>(back, indent);
    }

    public String toString(Expr e) throws IOException {
        out.beginC(0);
        ExprToOut(e);
        out.end().close();
        return back.getString();
    }
    private void ExprToOut(Expr expr) {
        /*
        if (expr instanceof ExprBad){
            ExprBadToOut((ExprBad)expr);
        } else if (expr instanceof ExprBadCall){
            ExprBadCallToOut((ExprBadCall)expr);
        } else if (expr instanceof ExprBadJoin){
            ExprBadJoinToOut((ExprBadJoin)expr);
        } else 
        */
        if (expr instanceof ExprBinary){
            ExprBinaryToOut((ExprBinary)expr);
        } else if (expr instanceof ExprCall){
            ExprCallToOut((ExprCall)expr);
        } else if (expr instanceof ExprChoice){
            ExprChoiceToOut((ExprChoice)expr);
        } else if (expr instanceof ExprConstant){
            ExprConstantToOut((ExprConstant)expr);
        } else if (expr instanceof ExprITE){
            ExprITEToOut((ExprITE)expr);
        } else if (expr instanceof ExprLet){
            ExprLetToOut((ExprLet)expr);
        } else if (expr instanceof ExprList){
            ExprListToOut((ExprList)expr);
        } else if (expr instanceof ExprQt){
            ExprQtToOut((ExprQt)expr);
        } else if (expr instanceof ExprUnary){
            ExprUnaryToOut((ExprUnary)expr);
        } else if (expr instanceof ExprVar){
            ExprVarToOut((ExprVar)expr);
        } else if (expr instanceof Sig){
            SigToOut((Sig)expr);
        } else if (expr instanceof Field){
            FieldToOut((Field)expr);
        } else DashErrors.missingExpr("ExprToOut ");
    }
    /*
    private void ExprBad(ExprBad expr) {
        StringBuilder tempOut = new StringBuilder();
        expr.toString(tempOut, -1);
        out.print(tempOut.toString());
    }

    private void ExprBadCall(ExprBadCall expr) {
        out.print(cleanLabel(expr.fun.label)).print('[').beginCInd();
        for (int i = 0; i < expr.args.size(); i++) {
            if (i > 0)
                out.print(", ");
            Expr(expr.args.get(i));
        }
        out.end().print(']');
    }

    private void ExprBadJoin(ExprBadJoin expr) {
        Expr(expr.left);
        out.print('.');
        Expr(expr.right);
    }
    */
    private Boolean isBinary(Expr e) {
        return (e instanceof ExprBinary);
    }
    private void ExprBinaryToOut(ExprBinary expr) {
        if (expr.op == ExprBinary.Op.ISSEQ_ARROW_LONE) {
            out.print("seq ");
            ExprToOut(expr.right);
        }
        else if (expr.op == ExprBinary.Op.JOIN)
            ExprBinaryJoinToOut(expr);
        else if (expr.op == ExprBinary.Op.IMPLIES) {
            ExprToOut(expr.left);
            out.print(" => ").print("{ ");
            ExprToOut(expr.right);
            out.print(" } ");
        }
        // This used to ensure that binary expressions have proper braces around them
        else if ( isBinary(expr.right) || isBinary(expr.left)  ) {    
            if ( isBinary(expr.left) && !(exprOp(expr.left) == exprOp(expr)) && !(exprOp(expr.left) == ExprBinary.Op.JOIN)) {  
                out.print('{').print(' ');
                ExprToOut(expr.left);
                out.print(' ').print("}").print(' ').print(expr.op).print(' ');
            } else {
                ExprToOut(expr.left);
                out.print(' ').print(expr.op).print(' ');
            }
            if (isBinary(expr.right)  && !(exprOp(expr.right) == exprOp(expr)) && !(exprOp(expr.right) == ExprBinary.Op.JOIN)){   
                out.print('{').print(' ');
                ExprToOut(expr.right);
                out.print(' ').print("}");
            } else {
                ExprToOut(expr.right);
            }
        }
        else {
            ExprToOut(expr.left);
            out.print(' ').print(expr.op).print(' ');
            ExprToOut(expr.right);
        }
    }
    
    private void ExprBinaryJoinToOut(ExprBinary expr) {
        // The Alloy resolve dot joins (this) to a variable reference in a variable. We should not bring the ("this")
        // We also do not print (Snapshot <: ...)
        boolean clean = (expr.left.toString().equals("this") && isAfterAlloyResolveAll);

        if (expr.right.toString().charAt(0) == '(') {
            if (!clean) {
                ExprToOut(expr.left);
                out.print(expr.op);
            }
            ExprToOut(expr.right);
        }
        else {
            if (!clean) {
                ExprToOut(expr.left);
                out.print(expr.op).print(' ').print('(');
            }
            ExprToOut(expr.right);
            if (!clean) {
                out.print(")");
            }
        }
    }

    private void ExprCallToOut(ExprCall expr) {
        out.print(cleanLabel(expr.fun.label));
        if (expr.args.size() == 0)
            return;
        out.print('[').beginCInd();
        for (int i = 0; i < expr.args.size(); i++) {
            if (i > 0)
                out.print(", ");
            ExprToOut(expr.args.get(i));
        }
        out.print(']').end();
    }

    private void ExprChoiceToOut(ExprChoice expr) {
        out.print("<");
        for (Expr e : expr.choices) {
            ExprToOut(e);
            out.print(";");
        }
        out.print(">");
    }

    private void ExprConstantToOut(ExprConstant expr) {
        if (expr.op == ExprConstant.Op.NUMBER)
            out.print(expr.num);
        else if (expr.op == ExprConstant.Op.STRING)
            out.print(expr.string);
        else
            out.print(expr.op);
    }

    private void ExprITEToOut(ExprITE expr) {
        out.print('(').beginCInd();
        ExprToOut(expr.cond);
        out.print(" => ").brk(1,0);
        ExprToOut(expr.left);
        out.brk(1,-indent).print(" else ").print("{").brk(1,0);
        ExprToOut(expr.right);
        out.print(" }");
        out.brk(1,-indent).end().print(')');
    }

    private void ExprLetToOut(ExprLet expr) {
        out.print("(let ").print(cleanLabel(expr.var.label)).print("= ").print(expr.toString()).print(" | ");
        ExprToOut(expr.sub);
        out.print(')');
    }

    private void ExprListToOut(ExprList expr) {
        if (expr.op == ExprList.Op.AND ) {
            String op = " and";
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                ExprToOut(expr.args.get(i));
            }
        }
        else if (expr.op == ExprList.Op.OR) {
            String op = " or";
            out.print("{ ");
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                ExprToOut(expr.args.get(i));
            }
            out.print(" }");
        }
        else {
            out.print(expr.op).print("[").beginCInd().brk(1,0);
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(",").brk(1,0);
                ExprToOut(expr.args.get(i));
            }
            out.brk(1,-indent).end().print(']');
        }
    }

    private void ExprQtToOut(ExprQt expr) {
        boolean first = true;
        if (expr.op != ExprQt.Op.COMPREHENSION)
            out.print('(').print(expr.op).print(' ').beginCInd();
        else
            out.print('{').beginCInd();
        DeclsToOut(expr.decls);
        if (expr.op != ExprQt.Op.COMPREHENSION || !(expr.sub instanceof ExprConstant) || ((ExprConstant) expr.sub).op != ExprConstant.Op.TRUE) {
            out.print(" | ");
            ExprToOut(expr.sub);
        }
        if (expr.op != ExprQt.Op.COMPREHENSION)
            out.end().print(')');
        else
            out.end().print('}');
    }

    private void ExprUnaryToOut(ExprUnary expr) {
        switch (expr.op) {
            case SOMEOF :
                out.print("some ");
                break;
            case LONEOF :
                out.print("lone ");
                break;
            case ONEOF :
                out.print("one ");
                break;
            case SETOF :
                out.print("set ");
                break;
            case EXACTLYOF :
                out.print("exactly ");
                break;
            case CAST2INT :
                out.print("int[");
                ExprToOut(expr.sub);
                out.print(']');
                return;
            case CAST2SIGINT :
                out.print("Int[");
                ExprToOut(expr.sub);
                out.print(']');
                return;
            case PRIME :
                out.print('(');
                ExprToOut(expr.sub);
                out.print(")'");
                return;
            case RCLOSURE :
                out.print("* (");
                ExprToOut(expr.sub);
                out.print(")");
                return;
            case TRANSPOSE :
                out.print("~ (");
                ExprToOut(expr.sub);
                out.print(")");
                return;
            case CLOSURE :
                out.print("^ (");
                ExprToOut(expr.sub);
                out.print(")");
                return;
            case NOT :
                out.print("! {");
                ExprToOut(expr.sub);
                out.print("}");
                return;
            case NOOP :
                break;
            default :
                out.print(expr.op).print(' ');
        }
        ExprToOut(expr.sub);
    }

    private void ExprVarToOut(ExprVar expr) {
        out.print(cleanLabel(expr.label));
    }

    private void SigToOut(Sig sig) {
        out.print(cleanLabel(sig.label));
    }

    private void FieldToOut(Field field) {
        out.print("(").print(cleanLabel(field.label)).print(")");
    }

    // Helper method to print a list of declarations
    private void DeclsToOut(ConstList<Decl> decls) {
        boolean first = true;
        for (Decl decl : decls) {
            StringJoiner namesJoiner = new StringJoiner(",");
            if (decl.disjoint != null) {
                out.print("disj").print(" ");
            }
            decl.names.forEach(name -> namesJoiner.add(cleanLabel(name.label)));
            if (!first) {
                out.print(",");
            }
            first = false;
            out.print(namesJoiner.toString());
            out.print(": ");
            ExprToOut(decl.expr, out);
        }
    }

    // Helper method to change "{path/label}" to "label"
    private String cleanLabel(String label) {
        if (!label.contains("this/")) {
            return label;
        }
        if (label.endsWith("}") && label.startsWith("{")){
            label = label.substring(1,label.length()-1);
        }
        int index = label.lastIndexOf('/');
        if (index > -1) {
            label = label.substring(index+1);
        }
        return label;
    }

    
    private ExprBinary.Op exprOp (Expr expr) {
        if (expr instanceof ExprBinary)
            return ((ExprBinary) expr).op;
        return null;
    }

}