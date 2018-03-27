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

package edu.mit.csail.sdg.ast;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import javax.swing.JFrame;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Listener;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;

/** This interface represents an Alloy module. */

public interface Module extends Clause {

    /**
     * Returns the text of the "MODULE" line at the top of the file; "unknown" if
     * the line has not be parsed from the file yet.
     */
    public String getModelName();

    /**
     * Return the simplest path pointing to this Module ("" if this is the main
     * module)
     */
    public String path();

    /**
     * Return the list containing THIS MODULE and all modules reachable from this
     * module.
     */
    public SafeList< ? extends Module> getAllReachableModules();

    /**
     * Return the list of all relative filenames included from this MODULE.
     */
    public List<String> getAllReachableModulesFilenames();

    /**
     * Return the list containing UNIV, SIGINT, SEQIDX, STRING, NONE, and all sigs
     * defined in this module or a reachable submodule.
     */
    public ConstList<Sig> getAllReachableSigs();

    /**
     * Return the list containing all sigs defined in this module or a reachable
     * submodule.
     */
    public ConstList<Sig> getAllReachableUserDefinedSigs();

    /**
     * Returns an unmodifiable list of all signatures defined inside this module.
     */
    public SafeList<Sig> getAllSigs();

    /**
     * Return an unmodifiable list of all functions in this module.
     */
    public SafeList<Func> getAllFunc();

    /**
     * Return an unmodifiable list of all assertions in this module.
     */
    public ConstList<Pair<String,Expr>> getAllAssertions();

    /**
     * Return an unmodifiable list of all facts in this module.
     */
    public SafeList<Pair<String,Expr>> getAllFacts();

    /**
     * Return the conjunction of all facts in this module and all reachable
     * submodules (not including field constraints, nor including sig appended
     * constraints)
     */
    public Expr getAllReachableFacts();

    /**
     * Return an unmodifiable list of all commands in this module.
     */
    public ConstList<Command> getAllCommands();

    /**
     * Add a global expression; if the name already exists, it is removed first.
     */
    public void addGlobal(String name, Expr value);

    /**
     * Display this object (and so objects) as a tree; if listener!=null, it will
     * receive OurTree.Event.SELECT events.
     */
    public JFrame showAsTree(Listener listener);

    /**
     * Parse one expression by starting fromt this module as the root module.
     */
    public Expr parseOneExpressionFromString(String input) throws Err, FileNotFoundException, IOException;
}
