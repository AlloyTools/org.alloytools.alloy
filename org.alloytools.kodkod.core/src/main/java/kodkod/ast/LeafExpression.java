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

/**
 * An expression with no children. {@link kodkod.ast.Relation Relation} and
 * {@link kodkod.ast.Variable Variable} are examples of leaf exressions. Two
 * leaf expressions are equal if and only if they refer to the same object. That
 * is, leaf1.eauls(leaf2) <=> leaf1 == leaf2. A leaf has a name, which is
 * basically a comment for the purpose of printing, viewing, etc. The name has
 * no meaning otherwise.
 *
 * @specfield name: String
 * @specfield arity: int
 * @specfield no children
 * @author Emina Torlak
 */
public abstract class LeafExpression extends Expression {

    private final int    arity;
    private final String name;

    /**
     * Constructs a leaf with the specified name and arity
     *
     * @ensures this.name' = name && this.arity' = arity
     * @throws IllegalArgumentException arity < 1
     */
    LeafExpression(String name, int arity) {
        if (arity < 1) {
            throw new IllegalArgumentException("Arity must be at least 1: " + arity);
        }
        this.name = name;
        this.arity = arity;
    }

    /**
     * Returns the arity of this leaf.
     *
     * @return this.arity
     */
    @Override
    public final int arity() {
        return arity;
    }

    /**
     * Returns the name of this leaf.
     *
     * @return this.name
     */
    public final String name() {
        return name;
    }

    /**
     * {@inheritDoc}
     *
     * @see kodkod.ast.Node#toString()
     */
    @Override
    public String toString() {
        return name;
    }

}
