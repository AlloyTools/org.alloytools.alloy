package ca.uwaterloo.watform.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

public class DashToStringAlloyAST {
	
	static String alloyModel = "";
	
    public static void printAlloyModel(DashModule module) throws IOException {

        printSigs(module);
        printPreds(module);
        printFacts(module);

        BufferedWriter writer = new BufferedWriter(new FileWriter(DashOptions.outputDir + ".als"));
        writer.write(alloyModel);

    	System.out.println(alloyModel);
        writer.close();
    }
    
    private static void printSigs(DashModule module) {
    	for(Sig sig: module.sigs.values()) {
    		if(sig.isAbstract != null)
    			alloyModel += ("abstract ");
    		if(sig.isOne != null)
    			alloyModel += ("one ");
    		
    		alloyModel += ("sig " + sig.label + " extends " + ((PrimSig) sig).parent + " {");
    		
    		if(sig.realFields.size() > 0)
    			alloyModel += '\n';
    		for(Field f: sig.realFields) {
    			for(ExprHasName name: f.decl.names)
    				alloyModel += (name.toString());
    			alloyModel += (": " + f.decl.expr + '\n');
    		}
    		
    		alloyModel += "}\n";
    	}
		alloyModel += "\n";
    }
    
    private static void printPreds(DashModule module) {
    	for(ArrayList<Func> funcs: module.funcs.values()) {
    		for(Func func: funcs) { 		
	    		alloyModel += ("pred " + func.label);
	    		
	    		if(func.decls.size() > 0)
	    			alloyModel += ("[");	    			
    			for(Decl decl: func.decls) {
    				for(ExprHasName name: decl.names) {
    					alloyModel += (name + ", ");
    				}
        			alloyModel += (": " + decl.expr + ", ");
    			}
	    		if(func.decls.size() > 0)
	    			alloyModel += ("]");
    			
    			alloyModel += "{\n";
    			alloyModel += (func.body.toString());   			    		
	    		alloyModel += "\n}\n\n";
    		}  
    	}   	
    }
    
    private static void printFacts(DashModule module) {
    	for(Pair<String,Expr> fact: module.facts) {		
    		alloyModel += ("fact {\n" + fact.b.toString() + "\n}\n");	    		  		  
    	}   	
    }
}
