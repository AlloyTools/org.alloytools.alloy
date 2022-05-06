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
import edu.mit.csail.sdg.ast.ExprBinary;

public class DashModuleToString {
	
	static int indent = 4;
    static int lineWidth = 120;
    static Boolean transitionLabelPrinted = false;
    static Boolean eventLabelPrinted = false;
    static String exprBinary = "EXPRBINARY";

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
		printAsserts(module, out);
		printCommands(module, out);
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
				if((!open.alias.equals(open.filename.substring(open.filename.indexOf("/") + 1))) && !open.alias.contains("$")) {
					out.print(" as ").print(open.alias);
				}
			}
			out.brk();
		}
		out.brk();
	}

    private static void printSigs(DashModule module, DataLayouter<NoExceptions> out) {
    	for(Sig sig: module.sigs.values()) {
    		printComments(module, sig.label, out);
    		
    		if(sig.isAbstract != null)
    			out.print("abstract ");
    		if(sig.isOne != null)
    			out.print("one ");
    		if(sig.isVariable != null)
    			out.print("var ");


            out.print("sig ");
			printSig(sig, out);
			// No need to print "extends" if this is a "var" signature
			if (sig.isVariable == null) {
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
			} else {
				out.print(" in ");
				
				System.out.println("Sig: " + sig.label + " Field Size: " + sig.getFields().size());
	    		if(sig.getFields().size() > 0) { 
	                for(Field f: sig.getFields()) {
	                    printExpr(f.decl().expr, out);
	                }
	                out.brk();
	            }
			}
    	}
		out.brk();
    }

    private static void printPreds(DashModule module, DataLayouter<NoExceptions> out) {
    	for(ArrayList<Func> funcs: module.funcs.values()) {
			for (Func func : funcs) {
				printComments(module, func.label, out);
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
    		printComments(module, fact.a, out);
			printComments(module, fact.b.toString(), out);
			out.print("fact ");
			if (!fact.a.contains("$")) {
				out.print(fact.a);
			}
            out.print(" {").beginCInd().brk(1,0);
			printExpr(fact.b,out);
			out.brk(1,-indent).end().print("}").brk().brk();
    	}
    }
    
    private static void printAsserts(DashModule module, DataLayouter<NoExceptions> out) {
    	for(String asserts: module.asserts.keySet()) {
			out.print("assert").print(' ').print(asserts).print(" {").beginCInd().brk(1,0);
			printExpr(module.asserts.get(asserts),out);
			out.brk(1,-indent).end().print("}").brk().brk();
    	}
    }
    
    private static void printCommands(DashModule module, DataLayouter<NoExceptions> out) {
    	for(Command command: module.commands) {
    		out.print(command.toString().substring(0, 1).toLowerCase() + command.toString().substring(1));
    		out.brk();
    	}
    	out.brk().brk();
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
		else if (expr.op == ExprBinary.Op.JOIN)
			printExprBinaryJoin(expr, out);
		else if (expr.op == ExprBinary.Op.IMPLIES) {
			printExpr(expr.left, out);
			out.print(" => ").print("{ ");
			printExpr(expr.right, out);
			out.print(" } ");
		}
		// This used to ensure that binary expressions have proper braces around them
		else if(exprType(expr.right).equals(exprBinary) || exprType(expr.left).equals(exprBinary)) {	
			if (exprType(expr.left).equals(exprBinary) && !(exprOp(expr.left) == exprOp(expr)) && !(exprOp(expr.left) == ExprBinary.Op.JOIN)){	
				out.print('{').print(' ');
				printExpr(expr.left, out);
				out.print(' ').print("}").print(' ').print(expr.op).print(' ');
			}
			else{
				printExpr(expr.left, out);
				out.print(' ').print(expr.op).print(' ');
			}
			if (exprType(expr.right).equals(exprBinary) && !(exprOp(expr.right) == exprOp(expr)) && !(exprOp(expr.right) == ExprBinary.Op.JOIN)){	
				out.print('{').print(' ');
				printExpr(expr.right, out);
				out.print(' ').print("}");
			}
			else{
				printExpr(expr.right, out);
			}
		}
		else {
			printExpr(expr.left, out);
			out.print(' ').print(expr.op).print(' ');
			printExpr(expr.right, out);
		}
	}
	
	private static void printExprBinaryJoin(ExprBinary expr, DataLayouter<NoExceptions> out) {
		printExpr(expr.left, out);
		if (expr.right.toString().charAt(0) == '(') {
			out.print(expr.op);
			printExpr(expr.right, out);
		}
		else {
			out.print(expr.op).print(' ').print('(');
			printExpr(expr.right, out);
			out.print(")");
		}
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
        if (expr.op == ExprList.Op.AND ) {
            String op = " and";
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                printExpr(expr.args.get(i), out);
            }
        }
        else if (expr.op == ExprList.Op.OR) {
            String op = " or";
            out.print("{ ");
            for (int i = 0; i < expr.args.size(); i++) {
                if (i > 0)
                    out.print(op).brk(1,0);
                printExpr(expr.args.get(i), out);
            }
            out.print(" }");
        }
        else {
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
			out.print('(').print(expr.op).print(' ').beginCInd();
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
			case RCLOSURE :
				out.print("*(");
				printExpr(expr.sub, out);
				out.print(")");
				return;
			case NOT :
				out.print("! {");
				printExpr(expr.sub, out);
				out.print("}");
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
			printExpr(decl.expr, out);
		}
	}

	// Helper method to change "{path/label}" to "label"
    private static String cleanLabel(String label) {
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
    
    private static String exprType(Expr expr) {	
    	if (expr instanceof ExprBinary)
    		return exprBinary;
    	return "";
    }
    
    private static ExprBinary.Op exprOp (Expr expr) {
    	if (expr instanceof ExprBinary)
    		return ((ExprBinary) expr).op;
    	return null;
    }
    
    private static void printComments(DashModule module, String reference, DataLayouter<NoExceptions> out) {
    	if (reference.equals("this/StateLabel")) {
    		out.brk().print("/***************************** STATE SPACE ************************************/").brk(); 
    	}
    	if ((reference.equals("this/EventLabel") && !eventLabelPrinted)) {
    		out.brk().print("/***************************** EVENTS SPACE ************************************/").brk(); 
    		eventLabelPrinted = true;
    	}
    	if (reference.equals("this/TransitionLabel") && !transitionLabelPrinted) {
    		out.brk().print("/***************************** TRANSITION SPACE ************************************/").brk(); 
    		transitionLabelPrinted = true;
    	}
    	if (reference.equals("stepUtil/BaseSnapshot")) {
    		out.print("// Snapshot Definition").brk(); 
    	}
    	if (reference.contains("pre_")) {
    		out.print("// // Predicates for the " + reference.substring(reference.indexOf('_')) + " transition.").brk(); 
    	}
    	if (reference.equals("this/init")) {
    		out.print("/* Overview ").brk(); 
    		out.print(" * init[] determines whether a snapshot is initial,").brk();
    		out.print(" * small_step [s,s_next] determines if a pair of Snapshots is a small step,").brk();
    		out.print("*/").brk();
    	}
    	if (reference.equals("this/operation")) {
    		out.print("/***************************** MODEL DEFINITION *******************************/").brk(); 
    	}
    	if (reference.equals("this/isEnabled")) {
    		out.print("// Test whether any transitions are enabled. A transition is enabled if the Snapshot satisfies its pre-condition").brk(); 
    	}
    	if (reference.equals("this/testIfNextStable")) {
    		out.print("// Evaluates to true if the next Snapshot is stable. The next Snapshot will be stable if no more transitions will").brk();
    		out.print("// be enabled after taking the current transition ").brk(); 
    	}
    	if (reference.equals("this/equals")) {
    		out.print("// Test whether two consequtive Snapshots are equal. Two Snapshots are equal if they have the same set of active").brk();
    		out.print("// control states, events generated, transitions taken in the big step, and system variables ").brk(); 
    	}
    	if (reference.equals("this/reachabilityAxiom")) {
    		out.print("/****************************** SIGNIFICANCE AXIOMS ****************************/").brk().brk(); 
    		out.print("/* This axiom ensures that all the snapshots considered during").brk(); 
    		out.print("   analysis must be reachable from an initial snapshot */").brk(); 
    	}
    	if (reference.equals("this/operationsAxiom")) {
    		out.print("/* This axiom states that every transition defined in a model is ").brk(); 
    		out.print("   represented by a pair of snapshots in the transition relation */").brk(); 
    	}
    	if (reference.equals("traces")) {
    		out.print("/* Create a Trace for the Model. This fact defines the following: ").brk();
    		out.print("   The first Snapshot in the ordering module should conforn to the initial conditions.").brk();
    		out.print("   A small step must be taken by consequetive Snapshots in the ordering module.").brk();
    		out.print("   A Snapshot that has not completed a big step (i.e. is not stable) must take a next step.").brk();
    		out.print("   The last Snapshot in a trace must be stable.").brk();
    		out.print("*/").brk();
    	}
    	if (reference.equals("different_atoms")) {
    		out.print("/* This fact defines the following:").brk();
    		out.print("   Consequtive snapshots that have the same set of active control states, events generated, transitions taken in the big step, and system variables are equal").brk();
    		out.print("*/").brk();
    	}
    	if (reference.equals("tcmc")) {
    		out.print("/* This connects the model to the CTL module to allow for CTL TCMC */").brk();
    	}
    }
}