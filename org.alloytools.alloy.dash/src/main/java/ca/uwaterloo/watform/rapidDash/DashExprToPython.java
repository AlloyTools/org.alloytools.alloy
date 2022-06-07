package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.ast.DashDoExpr;
import ca.uwaterloo.watform.ast.DashWhenExpr;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;


/*
    a class used to translate expressions to Python code
 */
public class DashExprToPython<ExprType> {
    private ExprType specialExpr;
    private StringBuilder sb;

    public DashExprToPython(ExprType specialExpr){
        this.specialExpr = specialExpr;
        this.sb = new StringBuilder();

        // TODO: currently only support DashWhenExpr
        this.parseExpr();
    }

    @Override
    public String toString() {
        return this.sb.toString();
    }

    // generate python expressions
    private void parseExpr(){
        // TODO: need to handle predicates with multiple lines
        if(specialExpr instanceof DashWhenExpr){
            sb.append(genExpr(((DashWhenExpr)this.specialExpr).expr, ((DashWhenExpr)this.specialExpr).exprList.size()));
        } else if (specialExpr instanceof DashDoExpr){
            // TODO: Do expr should be different since actions are needed, not just evaluation statements
        }
    }

    // print the expr tree using pre-order
    private String genExpr(Expr node, int size) {
        // TODO: currently, the second parameter is redundant

        // check type, there are two types of expr
        if (node instanceof ExprUnary) {
            // TODO: is sub always a binary?

            ExprUnary unaryNode = (ExprUnary) node;
            return(UnaryOp2PythonOp(unaryNode.op, unaryNode.sub));
        } else if (node instanceof ExprBinary) {
            // TODO: will BinaryExpr have sub nodes?

            // TODO: will need to replace left and right with signature names

            ExprBinary binaryNode = (ExprBinary) node;
            return(BinaryOp2PythonOp(binaryNode));
        } else if (node instanceof ExprVar){
            return node.toString();
        }else{
            // under development, use this to catch more types that could be useful
            System.out.println("More types: " + node.getClass());
        }
        return "";
    }

    // translate Unary operation, also returns the empty space
    private String UnaryOp2PythonOp(ExprUnary.Op op, Expr node){
        String res = " ";
        switch (op){
            case SOMEOF:
                res = " ";
                break;
            case LONEOF:
                res = " ";
                break;
            case ONEOF:
                res = " ";
                break;
            case SETOF:
                res = " ";
                break;
            case EXACTLYOF:
                res = " ";
                break;
            case NOT:        // TODO: this part assumes the inner expression is a statement that evaluates to true or false
                res = "not(" + this.genExpr(node,1) + ")";
                break;
            case AFTER:
                res = " ";
                break;
            case ALWAYS:
                res = " ";
                break;
            case EVENTUALLY:
                res = " ";
                break;
            case BEFORE:
                res = " ";
                break;
            case HISTORICALLY:
                res = " ";
                break;
            case ONCE:
                res = " ";
                break;
            case NO:        // TODO: this part assumes the inner expression is a signature instance that is an object
                res = this.genExpr(node,1) + " is None";
                break;
            case SOME:      // TODO: this part assumes the inner expression is a signature instance that is an object
                res = this.genExpr(node,1) + " is not None";
                break;
            case LONE:
                res = " ";
                break;
            case ONE:
                res = " ";
                break;
            case TRANSPOSE:
                res = " ";
                break;
            case PRIME:
                res = " ";
                break;
            case RCLOSURE:
                res = " ";
                break;
            case CLOSURE:
                res = " ";
                break;
            case CARDINALITY:
                res = " ";
                break;
            case CAST2INT:
                res = " ";
                break;
            case CAST2SIGINT:
                res = " ";
                break;
            case NOOP:
                res = "";
                break;
        }
        return res;
    }

    // translate Binary operation, also returns the empty space
    private String BinaryOp2PythonOp(ExprBinary node){
        String res = " ";
        switch(node.op){
            case ARROW:
                res = " ";
                break;
            case ANY_ARROW_SOME:
                res = " ";
                break;
            case ANY_ARROW_ONE:
                res = " ";
                break;
            case ANY_ARROW_LONE:
                res = " ";
                break;
            case SOME_ARROW_ANY:
                res = " ";
                break;
            case SOME_ARROW_SOME:
                res = " ";
                break;
            case SOME_ARROW_ONE:
                res = " ";
                break;
            case SOME_ARROW_LONE:
                res = " ";
                break;
            case ONE_ARROW_ANY:
                res = " ";
                break;
            case ONE_ARROW_SOME:
                res = " ";
                break;
            case ONE_ARROW_ONE:
                res = " ";
                break;
            case ONE_ARROW_LONE:
                res = " ";
                break;
            case LONE_ARROW_ANY:
                res = " ";
                break;
            case LONE_ARROW_SOME:
                res = " ";
                break;
            case LONE_ARROW_ONE:
                res = " ";
                break;
            case LONE_ARROW_LONE:
                res = " ";
                break;
            case ISSEQ_ARROW_LONE:
                res = " ";
                break;
            case JOIN:
                res = " ";
                break;
            case DOMAIN:
                res = " ";
                break;
            case RANGE:
                res = " ";
                break;
            case INTERSECT:
                res = " ";
                break;
            case PLUSPLUS:
                res = " ";
                break;
            case PLUS:        // TODO: this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + " | " + this.genExpr(node.right, 1);
                break;
            case IPLUS:
                res = " ";
                break;
            case MINUS:        // TODO: this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + " - " + this.genExpr(node.right, 1);
                break;
            case IMINUS:
                res = " ";
                break;
            case MUL:
                res = " ";
                break;
            case DIV:
                res = " ";
                break;
            case REM:
                res = " ";
                break;
            case EQUALS:        // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " == " + this.genExpr(node.right, 1);
                break;
            case NOT_EQUALS:    // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " != " + this.genExpr(node.right, 1);
                break;
            case IMPLIES:
                res = " ";
                break;
            case LT:         // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " < " + this.genExpr(node.right, 1);
                break;
            case LTE:        // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " <= " + this.genExpr(node.right, 1);
                break;
            case GT:         // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " > " + this.genExpr(node.right, 1);
                break;
            case GTE:        // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " >= " + this.genExpr(node.right, 1);
                break;
            case NOT_LT:     // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " >= " + this.genExpr(node.right, 1);
                break;
            case NOT_LTE:    // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " > " + this.genExpr(node.right, 1);
                break;
            case NOT_GT:     // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " <= " + this.genExpr(node.right, 1);
                break;
            case NOT_GTE:    // TODO: this part assumes this part assumes inner expression are a signature instances and are comparable
                res = this.genExpr(node.left, 1) + " < " + this.genExpr(node.right, 1);
                break;
            case SHL:
                res = " ";
                break;
            case SHA:
                res = " ";
                break;
            case SHR:
                res = " ";
                break;
            case IN:            // TODO: this part assumes inner expression are a signature instances and are sets
                res = this.genExpr(node.left, 1) + ".issubset(" + this.genExpr(node.right, 1) + ")";
                break;
            case NOT_IN:        // TODO: this part assumes inner expression are a signature instances and are sets
                res = "not(" + this.genExpr(node.left, 1) + ".issubset(" + this.genExpr(node.right, 1) + "))";
                break;
            case AND:           // TODO: this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") and (" + this.genExpr(node.right, 1) + ")";
                break;
            case OR:            // TODO: this part assumes the inner expression is a statement that evaluates to true or false
                res = "(" + this.genExpr(node.left, 1) + ") or (" + this.genExpr(node.right, 1) + ")";
                break;
            case IFF:
                res = " ";
                break;
            case UNTIL:
                res = " ";
                break;
            case RELEASES:
                res = " ";
                break;
            case SINCE:
                res = " ";
                break;
            case TRIGGERED:
                res = " ";
                break;
        }
        return res;
    }
}
