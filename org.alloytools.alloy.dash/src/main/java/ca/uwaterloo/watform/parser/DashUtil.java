/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package ca.uwaterloo.watform.parser;

import static edu.mit.csail.sdg.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.ast.Sig.SIGINT;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprUnary.Op;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Type.ProductType;
import edu.mit.csail.sdg.ast.VisitQueryOnce;

/**
 * This class provides convenience methods for calling the parser and the
 * compiler.
 */

public final class DashUtil {

    /**
     * Constructor is private, since this class never needs to be instantiated.
     */
    private DashUtil() {
    }

    // =============================================================================================================//

    /**
     * Go up the directory hierachy 0 or more times. <br>
     * For example, on a UNIX machine, goUp("/home/abc/def",1) will return
     * "/home/abc" <br>
     * For example, on a UNIX machine, goUp("/home/abc/def",2) will return "/home"
     *
     * @param filepath - this must be an absolute path
     * @param numberOfSteps - the number of steps to go up
     */
    private static String up(String filepath, int numberOfSteps) {
        while (numberOfSteps > 0) {
            numberOfSteps--;
            int i = filepath.lastIndexOf(File.separatorChar);
            if (i <= 0)
                return "";
            filepath = filepath.substring(0, i);
        }
        return filepath;
    }

    // =============================================================================================================//

    /**
     * Given the name of a module, and the filename for that module, compute the
     * filename for another module
     *
     * @param moduleA - must be a legal Alloy modulepath (eg. name) (eg.
     *            name/name/name) (must not start or end in '/')
     * @param fileA - the filename corresponding to moduleA
     * @param moduleB - must be a legal Alloy modulepath (eg. name) (eg.
     *            name/name/name) (must not start or end in '/')
     * @return the filename corresponding to moduleB
     */
    private static String computeModulePath(String moduleA, String fileA, String moduleB) {
        fileA = Util.canon(fileA); // Make sure it's a canonical absolute path
        if (moduleA.length() == 0)
            moduleA = "anything"; // Harmonizes the boundary case
        while (moduleA.length() > 0 && moduleB.length() > 0) {
            int a = moduleA.indexOf('/'), b = moduleB.indexOf('/');
            String headOfA = (a >= 0) ? moduleA.substring(0, a) : moduleA;
            String headOfB = (b >= 0) ? moduleB.substring(0, b) : moduleB;
            if (!headOfA.equals(headOfB) || a < 0 || b < 0) {
                // eg. util/boolean==/home/models/util/boolean.als, then
                // test=>/home/models/test.als"
                // eg. util/boolean==/home/models/util/boolean.als, then
                // sub/test=>/home/models/sub/test.als
                // eg. main==/home/models/main.als, then
                // test=>/home/models/test.als
                // eg. main==/home/models/main.als, then
                // sub/test=>/home/models/sub/test.als"
                int numberOfSlash = 0;
                for (int i = 0; i < moduleA.length(); i++)
                    if (moduleA.charAt(i) == '/')
                        numberOfSlash++;
                return up(fileA, numberOfSlash + 1) + File.separatorChar + moduleB.replace('/', File.separatorChar) + ".als";
            }
            moduleA = moduleA.substring(a + 1);
            moduleB = moduleB.substring(b + 1);
        }
        return ""; // This shouldn't happen, since there should always be some
                  // character after '/' in the module name
    }

    // =============================================================================================================//

    /**
     * Whether or not Int appears in the relation types found in these sigs
     */
    public static boolean areIntsUsed(Iterable<Sig> sigs, Command cmd) {
        /* check for Int-typed relations */
        for (Sig s : sigs) {
            for (Field f : s.getFields()) {
                for (ProductType pt : f.type()) {
                    for (int k = 0; k < pt.arity(); k++) {
                        if (pt.get(k) == SIGINT || pt.get(k) == SEQIDX)
                            return true;
                    }
                }
            }
        }

        if (cmd == null)
            return false;

        /* check expressions; look for CAST2SIGING (Int[]) */
        try {
            Object intTriggerNode;
            intTriggerNode = cmd.formula.accept(new VisitQueryOnce<Object>() {

                @Override
                public Object visit(ExprCall x) throws Err {
                    // skip integer arithmetic functions, because their
                    // arguments are always explicitly cast to SIGINT using
                    // Int[]
                    if (x.fun.label.startsWith("integer/"))
                        return null;
                    return super.visit(x);
                }

                @Override
                public Object visit(ExprUnary x) throws Err {
                    if (x.op == Op.CAST2SIGINT)
                        return x;
                    return super.visit(x);
                }
            });
            if (intTriggerNode != null)
                return true;
        } catch (Err e) {
        }

        return false;
    }

    // =============================================================================================================//

    /**
     * Helper method that recursively parse a file and all its included subfiles
     *
     * @param loaded - this stores the text files we've loaded while parsing; cannot
     *            be null
     * @param fc - if a file cannot be found, we consult this cache first before
     *            attempting to load it from disk/jar; cannot be null
     * @param pos - the position of the "open" statement
     * @param filename - the filename to open
     * @param root - the root module (this field is ignored if prefix=="")
     * @param prefix - the prefix for the file we are about to parse
     * @param thispath - the set of filenames involved in the current
     *            chain_of_file_opening
     */
    private static DashModule parseRecursivelyDash(List<Object> seenDollar, Map<String,String> loaded, Map<String,String> fc, Pos pos, String filename, DashModule root, String prefix, Set<String> thispath, int initialResolution) throws Err, FileNotFoundException, IOException {
        // Add the filename into a ArrayList, so that we can detect cycles in
        // the module import graph
        // How? I'll argue that (filename appears > 1 time along a chain) <=>
        // (infinite loop in the import graph)
        // => As you descend down the chain via OPEN, if you see the same FILE
        // twice, then
        // you will go into an infinite loop (since, regardless of the
        // instantiating parameter,
        // that file will attempt to OPEN the exact same set of files. leading
        // back to itself, etc. etc.)
        // <= If there is an infinite loop, that means there is at least 1
        // infinite chain of OPEN (from root).
        // Since the number of files is finite, at least 1 filename will be
        // repeated.


        if (thispath.contains(filename))
            throw new ErrorSyntax(pos, "Circular dependency in module import. The file \"" + (new File(filename)).getName() + "\" is imported infinitely often.");
        thispath.add(filename);
        // No cycle detected so far. So now we parse the file.
        DashModule u = DashUtil.parseDash(seenDollar, loaded, fc, root, 0, filename, prefix, initialResolution);
        if (prefix.length() == 0)
            root = u;

        // Here, we recursively open the included files
        for (ca.uwaterloo.watform.parser.DashModule.Open x : u.getOpens()) {
            String cp = Util.canon(computeModulePath(u.getModelName(), filename, x.filename)), content = fc.get(cp);
            try {
                if (content == null) {
                    content = loaded.get(cp);
                }
                if (content == null) {
                    content = fc.get(x.filename);
                    if (content != null)
                        cp = x.filename;
                }
                if (content == null) {
                    content = loaded.get(x.filename);
                    if (content != null)
                        cp = x.filename;
                }
                if (content == null) {
                    content = Util.readAll(cp);
                }
            } catch (IOException ex1) {
                try {
                    String newCp = cp.replaceAll("\\.als$", ".md");
                    content = Util.readAll(newCp);
                } catch (IOException exx) {

                    try {
                        String newCp = (Util.jarPrefix() + "models/" + x.filename + ".als").replace('/', File.separatorChar);
                        content = Util.readAll(newCp);
                        cp = newCp;
                    } catch (IOException ex) {
                    }
                }
            }
            loaded.put(cp, content);
            x.setResolvedFilePath(cp);
            DashModule y = parseRecursivelyDash(seenDollar, loaded, fc, x.pos, cp, root, (prefix.length() == 0 ? x.alias : prefix + "/" + x.alias), thispath, initialResolution);
            x.connect(y);
        }
        thispath.remove(filename); // Remove this file from the CYCLE DETECTION
                                  // LIST.
        return u;
    }

    /**
     * Whether the given command is a temporal model (either there are variable
     * sigs/fields or temporal operators in the formula).
     */
    public static boolean isTemporalModel(Iterable<Sig> sigs, Command cmd) {
        for (Sig sig : sigs) {
            if (sig.isVariable != null && !sig.builtin)
                return true;
            else {
                for (Decl dec : sig.getFieldDecls()) {
                    if (dec.isVar != null)
                        return true;
                }
            }
        }
        Object varTriggerNode;
        varTriggerNode = cmd.formula.accept(new VisitQueryOnce<Object>() {

            @Override
            public Object visit(ExprUnary x) throws Err {
                if (x.op == Op.AFTER || x.op == Op.BEFORE || x.op == Op.PRIME || x.op == Op.HISTORICALLY || x.op == Op.ALWAYS || x.op == Op.ONCE || x.op == Op.EVENTUALLY)
                    return x;
                return super.visit(x);
            }

            @Override
            public Object visit(ExprBinary x) throws Err {
                if (x.op == ExprBinary.Op.UNTIL || x.op == ExprBinary.Op.SINCE || x.op == ExprBinary.Op.TRIGGERED || x.op == ExprBinary.Op.RELEASES)
                    return x;
                return super.visit(x);
            }
        });
        if (varTriggerNode != null)
            return true;

        return false;
    }

    // =============================================================================================================//

    /**
     * Parses then typecheck the given input String as an Alloy expression from that
     * world
     *
     * @return the fully-typechecked expression if no error occurred
     * @throws Err if world==null or if any other error occurred
     */
    public static Expr parseOneExpression_fromString(DashModule world, String input) throws Err {
        try {
            if (world == null)
                throw new ErrorFatal("Cannot parse an expression with null world.");
            return world.parseOneExpressionFromString(input);
        } catch (IOException ex) {
            throw new ErrorFatal("IOException occurred: " + ex.getMessage(), ex);
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    // =============================================================================================================//

    /**
     * Read everything from "file" and parse it; if it mentions submodules, open
     * them and parse them too.
     *
     * @param rep - if nonnull, we will report compilation progress messages to it
     * @param loaded - a cache of files that have been pre-fetched (can be null if
     *            there were no prefetching)
     * @param filename - the main module we are parsing
     * @return the root Module which contains pointers to all submodules
     * @throws Err if an error occurred
     *             <p>
     *             And if loaded!=null, it will contain all the files needed for
     *             this parse, and furthermore, other entries will be deleted.
     */
    public static DashModule parseEverything_fromFileDash(A4Reporter rep, Map<String,String> loaded, String filename) throws Err {
        try {
            filename = Util.canon(filename);
            Set<String> thispath = new LinkedHashSet<String>();
            if (loaded == null)
                loaded = new LinkedHashMap<String,String>();
            Map<String,String> fc = new LinkedHashMap<String,String>(loaded);
            loaded.clear();
            List<Object> seenDollar = new ArrayList<Object>();
            DashModule root = parseRecursivelyDash(seenDollar, loaded, fc, new Pos(filename, 1, 1), filename, null, "", thispath, 1);
            root.seenDollar = seenDollar.size() > 0;
            //return DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, root);
            return root;
        } catch (FileNotFoundException ex) {
            throw new ErrorSyntax("File cannot be found.\n" + ex.getMessage(), ex);
        } catch (IOException ex) {
            throw new ErrorFatal("IOException occurred: " + ex.getMessage(), ex);
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    /**
     * Read everything from "file" and parse it; if it mentions submodules, open
     * them and parse them too.
     *
     * @param rep - if nonnull, we will report compilation progress messages to it
     * @param loaded - a cache of files that have been pre-fetched (can be null if
     *            there were no prefetching)
     * @param filename - the main module we are parsing
     * @param initialResolutionMode - use 1 for the historical behavior, and 2 for
     *            Alloy 4.2's new "universal implicit this" name resolution behavior
     * @return the root CompModule which contains pointers to all submodules
     * @throws Err if an error occurred
     *             <p>
     *             And if loaded!=null, it will contain all the files needed for
     *             this parse, and furthermore, other entries will be deleted.
     */
    public static DashModule parseEverything_fromFileDash(A4Reporter rep, Map<String,String> loaded, String filename, int initialResolutionMode) throws Err {
        try {
            filename = Util.canon(filename);
            Set<String> thispath = new LinkedHashSet<String>();
            if (loaded == null)
                loaded = new LinkedHashMap<String,String>();
            Map<String,String> fc = new LinkedHashMap<String,String>(loaded);
            loaded.clear();
            List<Object> seenDollar = new ArrayList<Object>();
            DashModule root = parseRecursivelyDash(seenDollar, loaded, fc, new Pos(filename, 1, 1), filename, null, "", thispath, initialResolutionMode);
            // if no sigs are defined by the user, add one
            if (root.getAllReachableUserDefinedSigs().isEmpty()) {
                root.addGhostSig();
            }
            root.seenDollar = seenDollar.size() > 0;
            return DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, root);
        } catch (FileNotFoundException ex) {
            throw new ErrorSyntax("File cannot be found.\n" + ex.getMessage(), ex);
        } catch (IOException ex) {
            throw new ErrorFatal("IOException occurred: " + ex.getMessage(), ex);
        } catch (Throwable ex) {
            if (ex instanceof Err)
                throw (Err) ex;
            else
                throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
        }
    }

    /**
     * @param rep - may be null
     * @param content - alloy model
     */
    public static DashModule parseEverything_fromStringDash(A4Reporter rep, String content) throws Err {
        if (rep == null)
            rep = new A4Reporter();
        try {
            File tmpAls = flushModelToFile(content, null);
            return DashUtil.parseEverything_fromFileDash(rep, null, tmpAls.getAbsolutePath());
        } catch (IOException ex) {
            throw new ErrorFatal("IOException occurred: " + ex.getMessage(), ex);
        }
    }

    /**
     * Saves the given alloy model to a file.
     *
     * @param model - alloy model
     * @param tmpAls - if null, a temporary file will be created and returned
     */
    public static File flushModelToFile(String model, File tmpAls) throws IOException {
        if (tmpAls == null) {
            tmpAls = File.createTempFile("alloy_heredoc", ".als");
            tmpAls.deleteOnExit();
        }
        try (BufferedOutputStream bos = new BufferedOutputStream(new FileOutputStream(tmpAls))) {
            bos.write(model.getBytes());
            bos.flush();
            return tmpAls;
        }
    }

    /* Dash Parsing. A change is required */
    static DashModule parseDash(List<Object> seenDollar, Map<String,String> loaded, Map<String,String> fc, DashModule root, int lineOffset, String filename, String prefix, int initialResolutionMode) throws Err, FileNotFoundException, IOException {
        DashModule module = DashParser.alloy_parseStream(seenDollar, loaded, fc, root, lineOffset, filename, prefix, initialResolutionMode);
        return module;
    }
}