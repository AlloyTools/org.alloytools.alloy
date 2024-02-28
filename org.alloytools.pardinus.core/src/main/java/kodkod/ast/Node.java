/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.ast;

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;


/**
 * A node in the abstract syntax tree (DAG).  A node
 * can accept a ReturnVisitor and have a sequence of
 * zero or more children.
 * 
 * @specfield children: int ->lone Node
 * @specfield components: set Node
 * @invariant children.Node = { i: int | 0 <= i < #children }
 * @invariant components= children[int]
 * @author Emina Torlak
 */
public abstract class Node {
    
    /**
     * Accepts the given visitor and returns the result
     * of the visit (i.e. the result of the call visitor.visit(this))
     * @return the result of being visited by the given visitor
     * @throws NullPointerException visitor = null
     */
    public abstract <E, F, D, I> Object accept(ReturnVisitor<E, F, D, I> visitor);
   
    /**
     * Accepts the given void visitor by calling visitor.visit(this).
     * @throws NullPointerException visitor = null
     */
    public abstract void accept(VoidVisitor visitor);

    /**
     * Returns a string representation of this node. 
     * For a pretty-printed string, use {@linkplain kodkod.util.nodes.PrettyPrinter}.
     * @return a string representation of this node
     * @see kodkod.util.nodes.PrettyPrinter
     */
    public abstract String toString();
}
