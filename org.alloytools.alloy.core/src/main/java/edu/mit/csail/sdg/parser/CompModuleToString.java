package edu.mit.csail.sdg.parser;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;

/*
 * Note: We cannot access the list of sigs/funcs/asserts/marcos as they are declared private.
 * However, the CompModule has getter functions which returns these lists. For example,
 * in order to get the list of sigs in a model, we use the getAllReachableUserDefinedSigs() function
 */

public class CompModuleToString {

    static String alloyModel = "";

    public static void toString(Module world, String filename) throws IOException {
        alloyModel = "";

        printSigs(world);
        printPreds(world);
        printFacts(world);

        //Use this to write the output to a file
        BufferedWriter writer = new BufferedWriter(new FileWriter(filename + "PRINTED" + ".als"));
        writer.write(alloyModel);

        //System.out.println("Representation of the Alloy Model: ");
        //System.out.println(alloyModel);
        writer.close();
    }

    private static void printSigs(Module module) {
        for (Sig sig : module.getAllReachableUserDefinedSigs()) {
            if (sig.isAbstract != null)
                alloyModel += ("abstract ");
            if (sig.isOne != null)
                alloyModel += ("one ");

            alloyModel += ("sig " + sig.label + " extends " + ((PrimSig) sig).parent + " {");

            if (sig.getFields().size() > 0)
                alloyModel += '\n';
            for (Field f : sig.getFields()) {
                for (ExprHasName name : f.decl().names)
                    alloyModel += (name.label);
                alloyModel += (": " + f.decl().expr + '\n');
            }

            alloyModel += "}\n";
        }
        alloyModel += "\n";
    }

    private static void printPreds(Module module) {
        for (Func func : module.getAllFunc()) {
            alloyModel += ("pred " + func.label);

            if (func.decls.size() > 0)
                alloyModel += ("[");
            for (Decl decl : func.decls) {
                for (ExprHasName name : decl.names) {
                    alloyModel += (name + ", ");
                }
                alloyModel += (": " + decl.expr + ", ");
            }
            if (func.decls.size() > 0)
                alloyModel += ("]");

            alloyModel += "{\n";
            alloyModel += (func.getBody().toString());
            alloyModel += "\n}\n\n";
        }
    }

    private static void printFacts(Module module) {
        for (Pair<String,Expr> fact : module.getAllFacts()) {
            alloyModel += ("fact {\n" + fact.b.toString() + "\n}\n");
        }
    }
}
