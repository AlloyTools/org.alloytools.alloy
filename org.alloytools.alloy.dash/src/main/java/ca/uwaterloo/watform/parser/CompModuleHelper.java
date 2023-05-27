// No state here
// just helper functions for adding elements to the module
// return a string that is what the Alloy text would be; avoids us having to print all of Alloy constructs

package ca.uwaterloo.watform.parser;

// tmp
import java.util.*;

import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import java.lang.StringBuilder;
import java.util.StringJoiner;

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
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;
//import static ca.uwaterloo.watform.alloyasthelper.ExprToString.*;

public class CompModuleHelper extends CompModule {

    private String space = " ";
    private String tab = DashStrings.tab;

    // this class is never instantiated
    public CompModuleHelper(CompModule world, String filename, String path) {
        super(world,filename,path);
    }

    public String addOpenSimple(String name, List<String> args, String aliasName) {
        ExprVar alias = (aliasName == null) ? null : createVar(aliasName);
        List<ExprVar> argsExprList = new ArrayList<ExprVar>();
        if (args != null)  
            for (String a: args) argsExprList.add(createVar(a));
        addOpen(null, null, createVar(name), argsExprList, alias);
        // build the string that is this open
        String s = DashStrings.openName + " "+name;
        if (args != null) {
            s += "[";
            StringJoiner j = new StringJoiner(", ");
            args.forEach(a -> j.add(a));
            s += j.toString();
            s += "]";
        }
        if (aliasName != null) s += " " + DashStrings.asName + " " + aliasName;
        return s+"\n";
    }

    /**
     *  adding signatures 
     * in CompModule, a signature has multiple related parts so can't just return a signature 
     * and let calling function add it to the module 
     * Alloy    public Sig addSig(Pos namePos, String name, ExprVar par, 
     *        List<ExprVar> parents, List<Decl> fields, Expr fact, Attr... attributes) throws Err {
     */
    
    public String addSigSimple(String name) {
        // sig name {}
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
        String s = new String();
        s += DashStrings.sigName + space + name + " {}\n";
        //System.out.println(s);
        return s;
    }

    public String addAbstractSigSimple(String name) {
        // abstract sig name {}
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
        String s = new String();
        s += DashStrings.abstractName + space + DashStrings.sigName + space;
        s += name + " {}\n";
        //System.out.println(s);
        return s;
    }

    public String addAbstractExtendsSigSimple(String extension, String extended) {
        // abstract sig extension extends extended {}
        addSig( 
            Pos.UNKNOWN,
            extension, 
            createVar(DashStrings.extendsName), 
            createExprVarList(new ArrayList<String>(Arrays.asList(extended))), 
            new ArrayList<Decl>(), 
            null,
            AttrType.ABSTRACT.makenull(Pos.UNKNOWN), 
            null, 
            null, 
            null, 
            null,
            null);
        String s = DashStrings.abstractName + space + DashStrings.sigName + space;
        s += extension + space + DashStrings.extendsName + space;
        s += extended;
        s += " {} \n"; 
        //System.out.println(s);
        return s;
    }

    public String addExtendsSigSimple(String extension, String extended) {
        // one sig extension extends extended {}
        addSig(
            Pos.UNKNOWN,
            extension, 
            createVar(DashStrings.extendsName), 
            createExprVarList(new ArrayList<String>(Arrays.asList(extended))), 
            new ArrayList<Decl>(), 
            null, 
            null, 
            null,
            null, 
            null, 
            null,
            null);
        String s = DashStrings.sigName + space;
        s += extension + space + DashStrings.extendsName + space;
        s += extended;
        s += " {} \n"; 
        //System.out.println(s);
        return s;
    }

    public String addOneExtendsSigSimple(String extension, String extended) {
        // one sig extension extends extended {}
        addSig(
            Pos.UNKNOWN,
            extension, 
            createVar(DashStrings.extendsName), 
            createExprVarList(new ArrayList<String>(Arrays.asList(extended))), 
            new ArrayList<Decl>(), 
            null, 
            null, 
            null,
            AttrType.ONE.makenull(Pos.UNKNOWN), 
            null, 
            null,
            null);
        String s = DashStrings.oneName + space + DashStrings.sigName + space;
        s += extension + space + DashStrings.extendsName + space;
        s += extended;
        s += " {} \n"; 
        //System.out.println(s);
        return s;
    }
    public String addSigWithDeclsSimple(String name, List<Decl> decls) {
        // sig name { decls }
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
        String s = DashStrings.sigName + space + name;
        s += " {\n"+tab;
        StringJoiner j = new StringJoiner(",\n"+tab);
        decls.forEach(i -> j.add(ppDecl(i)));
        s += j.toString() + "\n}\n";
        //System.out.println(s);
        return s;
    } 
    public String addSigExtendsWithDeclsSimple(String extension, String extended, List<Decl> decls) {
        // sig name { decls }
        addSig(
            Pos.UNKNOWN,
            extension, 
            createVar(DashStrings.extendsName), 
            createExprVarList(new ArrayList<String>(Arrays.asList(extended))), 
            decls, 
            null, 
            null, 
            null, 
            null, 
            null,
            null,
            null);
        String s = DashStrings.sigName + space;
        s += extension + space + DashStrings.extendsName + space;
        s += extended;
        s += " {\n";
        //s += ppDecls(decls);
        StringJoiner j = new StringJoiner(",\n"+tab);
        decls.forEach(i -> j.add(ppDecl(i)));
        s += j.toString() + "\n}\n";
        //System.out.println(s);
        return s;
    } 
    public String addOneSigWithDeclsSimple(String name, List<Decl> decls) {
        // sig name { decls }
        addSig(
            Pos.UNKNOWN,
            name, 
            null, 
            null, 
            decls, 
            null, 
            null, 
            null, 
            AttrType.ONE.makenull(Pos.UNKNOWN), 
            null,
            null,
            null);
        String s = DashStrings.sigName + space + name + space + "{\n";
        //s += ppDecls(decls);
        StringJoiner j = new StringJoiner(",\n");
        decls.forEach(i -> j.add(ppDecl(i)));
        s += j.toString() + "\n}\n";
        //System.out.println(s);
        return s;
    } 
    public String addVarSigSimple(String name, ExprVar typ) {
        // var sig s in typ {};
        addSig(
            Pos.UNKNOWN,
            name,
            createVar(DashStrings.inName), 
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
        String s = DashStrings.varName + space + DashStrings.sigName + space;
        s += name + space + DashStrings.inName + space;
        s += ppExpr(typ); 
        s += " { }\n";
        //System.out.println(s);
        return s;
    }

    public String addVarSigSimple(String name, List<ExprVar> typ) {
        // var sig s in typ {};
        addSig(
            Pos.UNKNOWN,
            name,
            createVar(DashStrings.inName), 
            typ,
            new ArrayList<Decl>(),
            null,
            null,
            null,
            null,
            null,
            null,
            AttrType.VARIABLE.makenull(Pos.UNKNOWN)
            );
        String s = DashStrings.varName + space + DashStrings.sigName + space;
        s += name + space + DashStrings.inName + space;
        s += ppExpr(((Expr) typ)); 
        s += " { }\n";
        //System.out.println(s);
        return s;
    }



    /**
     * adding functions/predicates 
     * 
     * Alloy: void addFunc(Pos p, Pos isPrivate, ExprVar n, Expr f, List<Decl> decls, Expr t, Expr v) 
     * f is a label
     * t is return type; null if predicate
     */
    public String addPredSimple(String name, List<Decl> decls, List<Expr> eList) {
        Expr body = createAndFromList(eList);
        addFunc(Pos.UNKNOWN, Pos.UNKNOWN, createVar(name), null, decls, null, body);
        String s = new String();
        s += DashStrings.predName + " " + name;
        if (!decls.isEmpty()) {
            s += " [\n\t";
            //s += ppDecls(decls);
            StringJoiner j = new StringJoiner(",\n\t");
            decls.forEach(i -> j.add(ppDecl(i)));
            s += j.toString() + "]";
        } 
        // we have to use our own printer
        // rather than expr.toString()
        // because that fcn does not include brackets
        // appropriately to get the correct associativity for joins
        //
        // later we could do something nicer for pred calls
        // but remember the predicate call to testIfNextStable is nested 
        // inside an ITE

        s += " {\n"+tab;
        StringJoiner sj = new StringJoiner("\n" + tab);   
        for (Expr e: eList) {
            //ExprToString eToString = new ExprToString(false);
            sj.add(ppExpr(e));
        }
        s += sj.toString();
        s += "\n}\n\n";
        return s;
    }

    /**
     * adding facts 
     * 
     * Alloy: void addFact(Pos pos, String name, Expr value)
     */
    
    public String addFactSimple(String name, List<Expr> eList) {
        Expr body = createAndFromList(eList);
        addFact(Pos.UNKNOWN,name,body);
        String s = new String();
        s += DashStrings.factName + " " + name + " {";
        StringJoiner j = new StringJoiner(", ");
        s += tab;
        StringJoiner sj = new StringJoiner("\n" + tab);   
        for (Expr e: eList) {
            //ExprToString eToString = new ExprToString(false);
            sj.add(ppExpr(e));
        }        
        s += sj.toString() + "\n";
        s+= "}\n\n";
        return s;
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

    public String getFilePath() {
        // complete path + filename of input file is
        // Pos of the "module" statement in CompModule
        return modulePos.filename;
    }
    // this seems incomplete -> DROP IT EVENTUALLY
    // also need to print facts
    /*
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
    */


}
