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
package kodkod.engine.solveengine;

/**
 * Most basic Expr instance.
 */
public class SatVar extends Expr{
    /** Name set to define the variable */
    private String name;
    /** In case the SATModel is satisfiable, here is a potential value of the variable, according to the solver */
    private Boolean value;
    /** Id to represent the variable in a cnf file */
    private Integer id;

    public SatVar(String name, Integer id) {
        this.name = name;
        this.value = null;
        this.id = id;
    }

    @Override
    public ListExpr convertToCnf() {
        return new AND(new OR(this));
    }

    @Override
    public String toString() {
        return this.name;
    }

    public String getName() {
        return name;
    }

    public Boolean getValue() {
        return value;
    }

    public Integer getId() {
        return id;
    }

    public String getCnfStr(){
        return this.id.toString();
    }

    public String getResult(){
        if  (this.value == null){
            return this.name +
                    ": not computed";
        } else {
            return this.name +
                    ": " +
                    this.value.toString();
        }
    }

    public void setValue(Boolean value) {
        this.value = value;
    }
}
