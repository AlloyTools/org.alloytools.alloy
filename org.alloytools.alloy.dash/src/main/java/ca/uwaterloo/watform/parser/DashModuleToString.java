package ca.uwaterloo.watform.parser;

import de.uka.ilkd.pp.DataLayouter;
import de.uka.ilkd.pp.NoExceptions;
import de.uka.ilkd.pp.StringBackend;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.StringJoiner;

public class DashModuleToString {
	
	static int indent = 4;
    static int lineWidth = 120;

    public static void toString(DashModule module) throws IOException {
		BufferedWriter writer = new BufferedWriter(new FileWriter(DashOptions.outputDir + ".als"));
		writer.write(getString(module));
		writer.close();
	}

    public static String getString(DashModule module) throws IOException {
		StringBackend back = new StringBackend(lineWidth);
		DataLayouter<NoExceptions> out = new DataLayouter<NoExceptions>(back, indent);
		out.beginC(0);
		printOpens(module, out);
		printSigs(module, out);
		printPreds(module, out);
		printFacts(module, out);
		out.end().close();
		return back.getString();
    }

	private static void printOpens(DashModule module, DataLayouter<NoExceptions> out) {
		for(DashModule.Open open: module.getOpens()) {
			out.print("open ").print(open.filename);
			if (open.args.size() > 0) {
				out.print("[");
				boolean first = true;
				for (String arg: open.args) {
					if (!first) {
						out.print(",");
					}
					first = false;
					out.print(arg);
				}
				out.print("]");
			}
			out.brk();
		}
		out.brk();
	}

    private static void printSigs(DashModule module, DataLayouter<NoExceptions> out) {
    	for(Sig sig: module.sigs.values()) {
    		if(sig.isAbstract != null)
    			out.print("abstract ");
    		if(sig.isOne != null)
    			out.print("one ");
    		
            out.print("sig ");
			printSig(sig, out);
			out.print(" extends ");
			printSig(((PrimSig) sig).parent,out);
			out.print(" {");
    		
    		if(sig.getFields().size() > 0) { 
                out.beginIInd().brk();
				boolean first = true;
                for(Field f: sig.getFields()) {
					StringJoiner namesJoiner = new StringJoiner(",");
					f.decl().names.forEach(name -> namesJoiner.add(cleanLabel(name.label)));
					if (!first) {
						out.print(",").brk();
					}
					first = false;
					out.print(namesJoiner.toString());
                    out.print(": ");
                    printExpr(f.decl().expr, out);
                }
                out.brk(1,-indent).end();
            }
    		out.print("}").brk();
    	}
		out.brk();
    }

    private static void printPreds(DashModule module, DataLayouter<NoExceptions> out) {
    	for(ArrayList<Func> funcs: module.funcs.values()) {
			for (Func func : funcs) {
				out.print("pred " + cleanLabel(func.label));

				if (func.decls.size() > 0)
					out.print("[").beginCInd();
				printDecls(func.decls, out);
				if (func.decls.size() > 0)
					out.end().print("]");

				out.print("{").beginCInd().brk();
				printExpr(func.getBody(), out);
				out.brk(1,-indent).end().print("}").brk().brk();
			}
		}
    }
    
    private static void printFacts(DashModule module, DataLayouter<NoExceptions> out) {
    	for(Pair<String,Expr> fact: module.facts) {
			out.print("fact {").beginCInd().brk(1,0);
			printExpr(fact.b,out);
			out.brk(1,-indent).end().print("}").brk();
    	}
    }
    
	private static void printExpr(Expr expr, DataLayouter<NoExceptions> out) {
		if (expr instanceof ExprBad){
			printExprBad((ExprBad)expr, out);
		} else if (expr instanceof ExprBadCall){
			printExprBadCall((ExprBadCall)expr, out);
		} else if (expr instanceof ExprBadJoin){
			printExprBadJoin((ExprBadJoin)expr, out);
		} else if (expr instanceof ExprBinary){
			printExprBinary((ExprBinary)expr, out);
		} else if (expr instanceof ExprCall){
			printExprCall((ExprCall)expr, out);
		} else if (expr instanceof ExprChoice){
			printExprChoice((ExprChoice)expr, out);
		} else if (expr instanceof ExprConstant){
			printExprConstant((ExprConstant)expr, out);
		} else if (expr instanceof ExprITE){
			printExprITE((ExprITE)expr, out);
		} else if (expr instanceof ExprLet){
			printExprLet((ExprLet)expr, out);
		} else if (expr instanceof ExprList){
			printExprList((ExprList)expr, out);
		} else if (expr instanceof ExprQt){
			printExprQt((ExprQt)expr, out);
		} else if (expr instanceof ExprUnary){
			printExprUnary((ExprUnary)expr, out);
		} else if (expr instanceof ExprVar){
			printExprVar((ExprVar)expr, out);
		} else if (expr instanceof Sig){
			printSig((Sig)expr, out);
		} else if (expr instanceof Field){
			printField((Field)expr, out);
		}
	}

	private static void printExprBad(ExprBad expr, DataLayouter<NoExceptions> out) {
		StringBuilder tempOut = new StringBuilder();
		expr.toString(tempOut, -1);
		out.print(tempOut.toString());
	}

	private static void printExprBadCall(ExprBadCall expr, DataLayouter<NoExceptions> out) {
		out.print(cleanLabel(expr.fun.label)).print('[').beginCInd();
		for (int i = 0; i < expr.args.size(); i++) {
			if (i > 0)
				out.print(", ");
			printExpr(expr.args.get(i), out);
		}
		out.end().print(']');
	}

	private static void printExprBadJoin(ExprBadJoin expr, DataLayouter<NoExceptions> out) {
		printExpr(expr.left, out);
		out.print('.');
		printExpr(expr.right, out);
	}

	private static void printExprBinary(ExprBinary expr, DataLayouter<NoExceptions> out) {
		if (expr.op == ExprBinary.Op.ISSEQ_ARROW_LONE)
			out.print("seq ");
		else if (expr.op == ExprBinary.Op.JOIN) {
			printExpr(expr.left, out);
			out.print(expr.op);
		}
		else {
			printExpr(expr.left, out);
			out.print(' ').print(expr.op).print(' ');
		}
		printExpr(expr.right, out);
	}

	private static void printExprCall(ExprCall expr, DataLayouter<NoExceptions> out) {
		out.print(cleanLabel(expr.fun.label));
		if (expr.args.size() == 0)
			return;
		out.print('[').beginCInd();
		for (int i = 0; i < expr.args.size(); i++) {
			if (i > 0)
				out.print(", ");
			printExpr(expr.args.get(i), out);
		}
		out.print(']').end();
	}

	private static void printExprChoice(ExprChoice expr, DataLayouter<NoExceptions> out) {
		out.print("<");
		for (Expr e : expr.choices) {
			printExpr(e, out);
			out.print(";");
		}
		out.print(">");
	}

	private static void printExprConstant(ExprConstant expr, DataLayouter<NoExceptions> out) {
		if (expr.op == ExprConstant.Op.NUMBER)
			out.print(expr.num);
		else if (expr.op == ExprConstant.Op.STRING)
			out.print(expr.string);
		else
			out.print(expr.op);
	}

	private static void printExprITE(ExprITE expr, DataLayouter<NoExceptions> out) {
		out.print('(').beginCInd();
		printExpr(expr.cond, out);
		out.print(" => ").brk(1,0);
		printExpr(expr.left, out);
		out.brk(1,-indent).print(" else ").brk(1,0);
		printExpr(expr.right, out);
		out.brk(1,-indent).end().print(')');
	}

	private static void printExprLet(ExprLet expr, DataLayouter<NoExceptions> out) {
		out.print("(let ").print(cleanLabel(expr.var.label)).print("= ").print(expr.toString()).print(" | ");
		printExpr(expr.sub, out);
		out.print(')');
	}

	private static void printExprList(ExprList expr, DataLayouter<NoExceptions> out) {
        if (expr.op == ExprList.Op.AND || expr.op == ExprList.Op.OR) {
            String op = expr.op == ExprList.Op.AND ? " and" : " or";
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                printExpr(expr.args.get(i), out);
            }
        } else {
            out.print(expr.op).print("[").beginCInd().brk(1,0);
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(",").brk(1,0);
                printExpr(expr.args.get(i), out);
            }
            out.brk(1,-indent).end().print(']');
        }
	}

	private static void printExprQt(ExprQt expr, DataLayouter<NoExceptions> out) {
		boolean first = true;
		if (expr.op != ExprQt.Op.COMPREHENSION)
			out.print('(').print(expr.op).print(' ').beginCInd().brk(1,0);
		else
			out.print('{').beginCInd();
		printDecls(expr.decls, out);
		if (expr.op != ExprQt.Op.COMPREHENSION || !(expr.sub instanceof ExprConstant) || ((ExprConstant) expr.sub).op != ExprConstant.Op.TRUE) {
			out.print(" | ");
			printExpr(expr.sub, out);
		}
		if (expr.op != ExprQt.Op.COMPREHENSION)
			out.end().print(')');
		else
			out.end().print('}');
	}

	private static void printExprUnary(ExprUnary expr, DataLayouter<NoExceptions> out) {
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
				printExpr(expr.sub, out);
				out.print(']');
				return;
			case CAST2SIGINT :
				out.print("Int[");
				printExpr(expr.sub, out);
				out.print(']');
				return;
			case PRIME :
				out.print('(');
				printExpr(expr.sub, out);
				out.print(")'");
				return;
			case NOOP :
				break;
			default :
				out.print(expr.op).print(' ');
		}
		printExpr(expr.sub, out);
	}

	private static void printExprVar(ExprVar expr, DataLayouter<NoExceptions> out) {
		out.print(cleanLabel(expr.label));
	}

	private static void printSig(Sig sig, DataLayouter<NoExceptions> out) {
		out.print(cleanLabel(sig.label));
	}

	private static void printField(Field field, DataLayouter<NoExceptions> out) {
		out.print("(").print(cleanLabel(field.sig.label)).print(" <: ").print(cleanLabel(field.label)).print(")");
	}

	// Helper method to print a list of declarations
	private static void printDecls(ConstList<Decl> decls, DataLayouter<NoExceptions> out) {
		boolean first = true;
		for (Decl decl : decls) {
			StringJoiner namesJoiner = new StringJoiner(",");
			decl.names.forEach(name -> namesJoiner.add(cleanLabel(name.label)));
			if (!first) {
				out.print(",").brk();
			}
			first = false;
			out.print(namesJoiner.toString());
			out.print(": ");
			printExpr(decl.expr, out);
		}
	}

	// Helper method to change "{path/label}" to "label"
    private static String cleanLabel(String label) {
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
