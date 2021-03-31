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

package edu.mit.csail.sdg.parser;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.ast.Browsable;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBad;
import edu.mit.csail.sdg.ast.ExprCustom;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.parser.CompModule.Context;

/** Immutable; this class represents a macro. */

final class Macro extends ExprCustom {

    /** If nonnull, this is a private macro. */
    final Pos                        isPrivate;

    /** The module that defined this. */
    private final CompModule         realModule;

    /** The name of the macro. */
    private final String             name;

    /** The list of parameters (can be an empty list) */
    private final ConstList<ExprVar> params;

    /**
     * The list of arguments (can be an empty list) (must be equal or shorter than
     * this.params)
     */
    private final ConstList<Expr>    args;

    /** The macro body. */
    private final Expr               body;

    /** Construct a new Macro object. */
    private Macro(Pos pos, Pos isPrivate, CompModule realModule, String name, List<ExprVar> params, List<Expr> args, Expr body) {
        super(pos, new ErrorFatal(pos, "Incomplete call on the macro \"" + name + "\""));
        this.realModule = realModule;
        this.isPrivate = isPrivate;
        this.name = name;
        this.params = ConstList.make(params);
        this.args = ConstList.make(args);
        this.body = body;
    }

    /** Construct a new Macro object. */
    Macro(Pos pos, Pos isPrivate, CompModule realModule, String name, List<ExprVar> params, Expr body) {
        this(pos, isPrivate, realModule, name, params, null, body);
    }

    Macro addArg(Expr arg) {
        return new Macro(pos, isPrivate, realModule, name, params, Util.append(args, arg), body);
    }

    Expr changePos(Pos pos) {
        return new Macro(pos, isPrivate, realModule, name, params, args, body);
    }

    /**
     * Instantiate it.
     *
     * @param warnings - the list that will receive any warning we generate; can be
     *            null if we wish to ignore warnings
     */
    Expr instantiate(Context cx, List<ErrorWarning> warnings) throws Err {
        if (cx.unrolls <= 0) {
            Pos p = span();
            return new ExprBad(p, toString(), new ErrorType(p, "Macro substitution too deep; possibly indicating an infinite recursion."));
        }
        if (params.size() != args.size())
            return this;
        Context cx2 = new Context(realModule, warnings, cx.unrolls - 1);
        for (int n = params.size(), i = 0; i < n; i++) {
            Expr tmp = args.get(i);
            if (!(tmp instanceof Macro))
                tmp = tmp.resolve(tmp.type(), warnings);
            cx2.put(params.get(i).label, tmp);
        }
        return cx2.check(body);
    }

    /** {@inheritDoc} */
    @Override
    public void toString(StringBuilder out, int indent) {
        if (indent < 0) {
            out.append(" macro\"").append(name).append("\" ");
        } else {
            for (int i = 0; i < indent; i++) {
                out.append(' ');
            }
            out.append("macro\"").append(name).append("\"\n");
        }
    }

    /** {@inheritDoc} */
    @Override
    public int getDepth() {
        int max = body.getDepth();
        for (Expr x : args) {
            int tmp = x.getDepth();
            if (max < tmp)
                max = tmp;
        }
        return 1 + max;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return name;
    }

    /** {@inheritDoc} */
    @Override
    public String getHTML() {
        return "<b>error</b> (parser or typechecker failed)";
    }

    /** {@inheritDoc} */
    @Override
    public List< ? extends Browsable> getSubnodes() {
        return new ArrayList<Browsable>(0);
    }

    public Macro copy() {
        return new Macro(pos, isPrivate, realModule, name, params, args, body);
    }

}
