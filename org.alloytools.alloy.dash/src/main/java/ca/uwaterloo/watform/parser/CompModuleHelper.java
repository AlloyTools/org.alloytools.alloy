// No state here
// just helper functions for adding elements to the module

package ca.uwaterloo.watform.parser;

// tmp
import java.util.*;

import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import java.lang.StringBuilder;

import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.ast.Attr.AttrType;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;

import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.alloyasthelper.AlloyExprHelper;


public class CompModuleHelper extends CompModule {

    // this class is never instantiated
    public CompModuleHelper(CompModule world, String filename, String path) {
        super(world,filename,path);
    }

    /**
     *  adding signatures 
     * in CompModule, a signature has multiple related parts so can't just return a signature 
     * and let calling function add it to the module 
     * Alloy    public Sig addSig(Pos namePos, String name, ExprVar par, 
     *        List<ExprVar> parents, List<Decl> fields, Expr fact, Attr... attributes) throws Err {
     */
    public void addSigSimple(String name) {
        addSig( 
            Pos.UNKNOWN,
            name, 
            null, 
            null, 
            new ArrayList<Decl>(), 
            null, 
            null, 
            null, 
            null, 
            null,
            null,
            null);
    }

    public void addAbstractSigSimple(String name) {
        addSig(
            Pos.UNKNOWN,
            name, 
            null, 
            null, 
            new ArrayList<Decl>(), 
            null,
            AttrType.ABSTRACT.makenull(Pos.UNKNOWN), 
            null, 
            null, 
            null, 
            null,
            null);
    }

    public void addAbstractExtendsSigSimple(String extension, String extended) {
        addSig( 
            Pos.UNKNOWN,
            extension, 
            AlloyExprHelper.createVar(DashStrings.extendsName), 
            AlloyExprHelper.createVarList(new ArrayList<String>(Arrays.asList(extended))), 
            new ArrayList<Decl>(), 
            null,
            AttrType.ABSTRACT.makenull(Pos.UNKNOWN), 
            null, 
            null, 
            null, 
            null,
            null);
    }

    public void addOneExtendsSigSimple(String extension, String extended) {
        addSig(
            Pos.UNKNOWN,
            extension, 
            AlloyExprHelper.createVar(DashStrings.extendsName), 
            AlloyExprHelper.createVarList(new ArrayList<String>(Arrays.asList(extended))), 
            new ArrayList<Decl>(), 
            null, 
            null, 
            null,
            AttrType.ONE.makenull(Pos.UNKNOWN), 
            null, 
            null,
            null);
    }
    public void addSigWithDeclsSimple(String name, ArrayList<Decl> decls) {
        addSig(
            Pos.UNKNOWN,
            name, 
            null, 
            null, 
            decls, 
            null, 
            null, 
            null, 
            null, 
            null,
            null,
            null); 
    } 
    /*
    public Sig addSig(Pos namePos, String name, ExprVar par, 
             List<ExprVar> parents, List<Decl> fields, Expr fact, Attr... attributes)
    */
    public void addVarSigSimple(String name, ExprVar typ) {
        // Electrum: var sig s in typ;
        addSig(
            Pos.UNKNOWN,
            name,
            AlloyExprHelper.createVar(DashStrings.inName), 
            Arrays.asList(typ),
            new ArrayList<Decl>(),
            null,
            null,
            null,
            null,
            null,
            null,
            AttrType.VARIABLE.makenull(Pos.UNKNOWN)
            );
    }

    public void addOpenSimple(String name, List<String> args, String aliasName) {
        ExprVar alias = (aliasName == null) ? null : AlloyExprHelper.createVar(aliasName);
        List<ExprVar> argsExprList = new ArrayList<ExprVar>();
        if (args != null)  
            for (String a: args) {
                argsExprList.add(AlloyExprHelper.createVar(a));
            }
        // problem: we can't add opens after other stuff has been parsed in the Alloy module
        addOpen(null, null, AlloyExprHelper.createVar(name), argsExprList, alias);
    }

    /**
     * adding functions/predicates 
     * 
     * Alloy: void addFunc(Pos p, Pos isPrivate, ExprVar n, Expr f, List<Decl> decls, Expr t, Expr v) 
     * f is a label
     * t is return type; null if predicate
     */
    public void addPredSimple(String name, List<Decl> decls, ArrayList<Expr> eList) {
        Expr body = AlloyExprHelper.createAnd(eList);
        addFunc(Pos.UNKNOWN, Pos.UNKNOWN, AlloyExprHelper.createVar(name), null, decls, null, body);
    }

    /**
     * adding facts 
     * 
     * Alloy: void addFact(Pos pos, String name, Expr value)
     */
    /*
    public void addFactSimple(String name, List<Expr> eList) {
        Expr body = createAnd(eList);
        alloy.addFact(Pos.UNKNOWN,name,body);
    }
    */

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

    public String getFilePath() {
        // complete path + filename of input file is
        // Pos of the "module" statement in CompModule
        return modulePos.filename;
    }
    // this seems incomplete -> DROP IT EVENTUALLY
    // also need to print facts
    public String sigsToString() {
        StringBuilder sb = new StringBuilder("");
        for(Sig sig: sigs.values()) {
            if(sig.isVariable != null)
                sb.append("var ");
            if (sig.builtin) 
                sb.append("builtin ");
            if (sig.isPrivate != null)
                sb.append("private ");
            if (sig.isAbstract != null)
                sb.append("abstract ");

            if (sig.isLone != null)
                sb.append("lone ");

            if (sig.isOne != null)
                sb.append("one ");

            if (sig.isOne != null)
                sb.append("some ");

            if (sig.isEnum != null)
                sb.append("enum ");
            sb.append("sig ");
            sb.append(cleanLabel(sig.label)).append(" ");
            if (sig.isSubsig != null && ((PrimSig) sig).parent.equals("univ")) {
                sb.append("extends ");
                sb.append(((PrimSig) sig).parent);
            } else if (sig.isSubset != null) {
                sb.append("in ");
                sb.append(((PrimSig) sig).parent);
            }
            
            sb.append(" {");
            for (Field f : sig.getFields()) {
                StringJoiner namesJoiner = new StringJoiner(",\n");
                f.decl().names.forEach(name -> namesJoiner.add(cleanLabel(name.label)));
                sb.append(namesJoiner.toString());
            }
            sb.append(cleanLabel(sig.label)).append("}\n");

        }
        return sb.toString();
    }
}
