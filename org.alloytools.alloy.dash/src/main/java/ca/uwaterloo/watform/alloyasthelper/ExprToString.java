package ca.uwaterloo.watform.alloyasthelper;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.StringJoiner;
import java.util.List;
import java.util.Collections;
import java.util.stream.Collectors;

import de.uka.ilkd.pp.DataLayouter;
import de.uka.ilkd.pp.NoExceptions;
import de.uka.ilkd.pp.StringBackend;


import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.core.DashRef;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.core.DashStrings;

/* 
    Notes on the pretty printer primitives
    .begin(boolean consistent, int spaces) - start block
    .beginC(x) = .begin(true,x)
    .end() - end block
    .print(string text)
    .brk(int spacesifnotbroken, int spacestoaddorsubtractfromindentifbroken)
    .brk(x) = .brk(x,0) 
    .brk() = .brk(1,0)
    .close() - finish the string

    consistent block means if break required then all have breaks
    inconsistent block means put as much as possible on a line
*/
public class ExprToString {

    int indent = DashStrings.tab.length();
    int lineWidth = 60;
    StringBackend back = new StringBackend(lineWidth);
    DataLayouter<NoExceptions> out = new DataLayouter<NoExceptions>(back, indent);;
    Boolean isAfterAlloyResolveAll;


    public ExprToString(boolean isAfterAlloyResolveAll) {
        this.isAfterAlloyResolveAll = isAfterAlloyResolveAll;
    }

    public String exprToString(Expr e)  {
        out.beginC(0);
        ExprToOut(e);
        out.end();
        out.close();
        return back.getString();
    }
    public String declToString(Decl d) {
        out.beginC(0);
        DeclToOut(d);
        out.end();
        out.close();
        return back.getString();        
    }
    private void ExprToOut(Expr expr) {
        
        /*
        if (expr instanceof ExprBad){
            ExprBadToOut((ExprBad)expr);
        
        } else if (expr instanceof ExprBadCall){
            ExprBadCallToOut((ExprBadCall)expr);
        */
        if (expr instanceof ExprBadJoin){
            ExprBadJoinToOut((ExprBadJoin)expr);
        } else if (expr instanceof ExprBinary) {
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
            //System.out.println(((ExprVar) expr).label);
            out.print(cleanLabel(((ExprVar) expr).label));
        } else if (expr instanceof Sig){
            out.print(cleanLabel(((Sig) expr).label));
        } else if (expr instanceof Field){
            out.print("(").print(cleanLabel(((Field) expr).label)).print(")");
        } else {
            DashErrors.missingExpr("ExprToOut :" +expr.getClass().getName());
        }
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
    */

    /*
    private Boolean isBinary(Expr e) {
        return (e instanceof ExprBinary);
    }
    */
    private void ExprBinaryToOut(ExprBinary expr) {
        //System.out.println(expr.op);
        if (DashRef.isDashRef(expr)) {
            // won't hit this case when outputting after translation to Alloy
            out.print(expr.toString());
        } else if (expr.op == ExprBinary.Op.ISSEQ_ARROW_LONE) {
            //TODO: this seems odd
            out.print("seq ");
            out.beginC(2);
            ExprToOut(expr.right);
            out.end();
            //out.print(")");
        } else if (expr.op == ExprBinary.Op.JOIN) {
            // there are really long join expressions
            // so don't make it a block
            //out.beginI(2);
            addBracketsIfNeeded(getLeft(expr));
            //out.brk(1,0);
            out.print(expr.op);
            //out.brk(1,0);
            addBracketsIfNeeded(getRight(expr));  
            //out.end();  
        } else {
            //System.out.println(expr.op);
            out.beginI(2);
            addBracketsIfNeeded(getLeft(expr));
            out.brk(1,0);
            out.print(expr.op);
            out.brk(1,0);
            addBracketsIfNeeded(getRight(expr));  
            out.end();     
        }
    }

/*
    private void addBracketsIfNeededNoBlocks(Expr expr) {
        Boolean bracketNotNeeded = 
            isExprVar(expr) || 
                (isExprUnary(expr) && 
                    !isExprCard(expr)&& 
                    !isExprRClosure(expr) && 
                    !isExprClosure(expr));
        if (!(isExprVar(expr) || (isExprUnary(expr) && !isExprCard(expr) ))) {
            //out.beginC(2);
            out.print("(");      
        }    
        ExprToOut(expr);
         if (!(isExprVar(expr) || (isExprUnary(expr) && !isExprCard(expr) ) )) {
            out.print(")");
            //out.end();
        }            
    } 
*/

    private void addBracketsIfNeeded(Expr expr) {
        Boolean bracketsNotNeeded = 
            isExprVar(expr) ||
            // 2024-02-20 NAD sig x { y: x -> (one k)} does not work
            // must be sig x { y: x -> one k}
            isExprUnary(expr) &&
                !isExprCard(expr)

            /*||
                removed b/c unary operators don't seem to always bind tightly
                (isExprUnary(expr) && 
                    !isExprCard(expr)&& 
                    !isExprRClosure(expr) && 
                    !isExprClosure(expr)) */
                    ;
        if (!bracketsNotNeeded) {
            //out.beginC(2);
            out.print("(");
        }
        ExprToOut(expr);
        if (!bracketsNotNeeded) {
            out.print(")");
            //out.end();
        }            
    }  

    private void ExprBadJoinToOut(ExprBadJoin expr) {
        addBracketsIfNeeded(expr.left);
        out.print('.');
        addBracketsIfNeeded(expr.right);
    }

    private void ExprCallToOut(ExprCall expr) {
        out.print(cleanLabel(expr.fun.label));
        if (expr.args.size() == 0)
            return;
        out.print('[');
        out.beginC(2);
        for (int i = 0; i < expr.args.size(); i++) {
            if (i > 0) out.print(", ");
            ExprToOut(expr.args.get(i));
        }
        out.end();
        out.print(']');

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
        out.beginC(2);
        out.print("{");
        addBracketsIfNeeded(expr.cond);
        out.print("=>");
        out.brk(1,indent);
        addBracketsIfNeeded(expr.left);
        out.brk(1,0);
        out.print("else");
        //{")
        out.brk(1,indent);
        addBracketsIfNeeded(expr.right);
        out.print("}");
        //out.print(" }");
        out.brk(1,-indent);
        out.end();
        //out.print(')');
    }

    private void ExprLetToOut(ExprLet expr) {
        out.print("(let");
        out.brk(1,0);
        out.print(cleanLabel(expr.var.label));
        out.brk(1,0);
        out.print("=");
        out.brk(1,0);
        ExprToOut(expr.expr); 
        out.brk(1,0);
        out.print("|");
        out.brk(1,0);
        out.beginC(2);
        ExprToOut(expr.sub);
        out.end();
        out.print(')');
    }

    private void ExprListToOut(ExprList expr) {
        //System.out.println(expr.op);
        if (expr.op == ExprList.Op.AND ) {
            String op = " &&";
            out.beginC(2);
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                addBracketsIfNeeded(expr.args.get(i));
            }
            out.end();
        }
        else if (expr.op == ExprList.Op.OR) {
            String op = " ||";
            out.print("{ ");
            out.beginC(2);
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0) {
                    out.print(op);
                    out.brk(1,0);
                }
                addBracketsIfNeeded(expr.args.get(i));
            }
            out.end();
            out.print(" }");
        }
        else {
            out.print(expr.op);
            out.print("[");
            out.beginCInd();
            out.brk(1,0);
            out.beginC(2);
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(",").brk(1,0);
                addBracketsIfNeeded(expr.args.get(i));
            }
            out.brk(1,-indent);
            out.end();
            out.print(']');
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
        //System.out.println(expr.op);
        switch (expr.op) {
            // special cases for the 
            // ones that the Alloy op.toString()
            // does not seem to print in a way that matches
            // how the symbol is input
            // e.g. set X becomes set of X
            case SOMEOF :
                out.print("some");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;
            case LONEOF :
                out.print("lone");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;
            case ONEOF :
                out.print("one");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;

            case EXACTLYOF :
                out.print("exactly");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;
            case SETOF :
                out.print("set");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;
            case CAST2INT :
                out.print("int[");
                ExprToOut(expr.sub);
                out.print(']');
                break;
            case CAST2SIGINT :
                out.print("Int[");
                ExprToOut(expr.sub);
                out.print(']');
                break;
            case PRIME :
                //TODO: perhaps this one should not exist?
                //TODO: other temporal formulas that should not exist?
                addBracketsIfNeeded(expr.sub);
                out.print("'");
                break;
            case RCLOSURE :
                out.print("*");
                out.brk(1,0);
                addBracketsIfNeeded(expr.sub);
                break;
            case TRANSPOSE :
                out.print("~");
                out.brk(1,0);
                addBracketsIfNeeded(expr.sub);
                break;
            case CLOSURE :
                out.print("^");
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
                break;
            case NOT :
                out.print("!");
                //out.brk(1,0);
                addBracketsIfNeeded(expr.sub);
                break;
            case NOOP :
                // { expr } is parsed as NOOP (expr)
                ExprToOut(expr.sub);
                break;
            default :
                // many operators print okay
                // e.g., one, 
                out.print(expr.op);
                out.brk(1);
                addBracketsIfNeeded(expr.sub);
        }

    }


    // Helper method to print a list of declarations
    private void DeclsToOut(List<Decl> decls) {
        //TODO add appropriate breaks here
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
            ExprToOut(decl.expr);
        }
    }

    private void DeclToOut(Decl decl) {
       if (decl.disjoint != null) {
            out.print("disj").print(" ");
        }
        if (decl.isVar != null) {
            out.print(DashStrings.varName + " ");
        }
        out.print(DashUtilFcns.strCommaList(decl.names));
        out.print(": ");
        ExprToOut(decl.expr);        
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


}