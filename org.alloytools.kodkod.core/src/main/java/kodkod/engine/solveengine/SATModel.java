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

import kodkod.engine.solveengine.enums.SolveStatusCode;

import java.util.ArrayList;
import java.util.HashMap;

import static java.lang.Math.abs;

/**
 * Class representing a whole SAT problem. Contains variables SatVar and constraints Expr to represent the model.
 *
 * Using addVariables, you add a variable and it returns it, so you can use the variable to build expressions
 * Those expressions can be added as SAT constraints with addConstraint
 *
 * The instance can call buildStrModel() to formatting all the constraints into a CNF file.
 * The instance can call solve() to call SolveEngine. The model will then directly be updated,
 * giving a value to each variable if Satisfiable.
 */
public class SATModel extends Model {
    /** HashMap of the variables, id -> name */
    private HashMap<Integer, String> variableNames;

    /** HashMap of the variables, name -> variable instance */
    private HashMap<String, SatVar> variables;

    /** List of all the constraints, as added*/
    private ArrayList<Expr> constraints;

    public SatVar getVariable(String varName) { return variables.get(varName); }

    public ArrayList<Expr> getConstraints() { return constraints; }

    public SolveStatusCode getSolveStatus() { return solveStatus; }

    public String getFileName() { return fileName; }

    public String getToken() { return token; }

    public void setToken(String token) { this.token = token; }

    /**
     * If the name does not finish by ".cnf", will add it to the fileName
     * @param modelName
     */
    public void setFileName(String modelName) {
        this.fileName = modelName + (modelName.endsWith(SEConfig.SAT_EXTENSION) ? "" : SEConfig.SAT_EXTENSION);
    }

    public String getVariableName(int variableId) { return variableNames.get(variableId); }

    public Integer getSleepTime() { return client.getSleepTimeSeconds(); }

    /**
     * Splits/translates the constraints into cnf clauses
     * @return the ArrayList of reduced Expr instances, each Expr is a row of the cnf file to be built
     * @throws UnsupportedOperationException if the code has been modified not properly
     */
    private ArrayList<Expr> constraintsToClauses() throws UnsupportedOperationException {
        ArrayList<Expr> clauses = new ArrayList<>();
        ArrayList<Expr> temContent;

        for (Expr constraint : constraints) {
            temContent = constraint.convertToCnf().getContent();
            clauses.addAll(temContent);
        }

        return clauses;
    }

    public SATModel(String token, String fileName, Integer sleepTime, Boolean interactiveMode) {
        super(token, fileName, sleepTime, interactiveMode);
        this.variableNames = new HashMap<>();
        this.variables = new HashMap<>();
        this.constraints = new ArrayList<>();
    }

    public SATModel(String token, String fileName, Integer sleepTime) { this(token, SEConfig.DEFAULT_MODEL_NAME, sleepTime, false); }
    public SATModel(String token, String fileName, Boolean interactivemode) { this(token, SEConfig.DEFAULT_MODEL_NAME, 2, interactivemode); }
    public SATModel(String token, String fileName) { this(token, fileName, 2, false); }
    public SATModel(String token) { this(token, SEConfig.DEFAULT_MODEL_NAME, 2, false); }

    /**
     * Creates a SatVar instance and adds it to the three hashmaps of the SATModel.
     * @param name of the variable
     * @param id the integer that will be used for the cnf model
     * @return the SatVar instance
     * @throws ExistingVariableException
     */
    public SatVar addVariable(String name, Integer id) throws ExistingVariableException {
        if(this.variables.containsKey(name)) {
            throw new ExistingVariableException("This name is already used by another variable");
        }

        this.variableNames.put(id, name);

        SatVar var = new SatVar(name, id);
        this.variables.put(name, var);

        return var;
    }

    /**
     * Will add a variable with a specified name. The id used by default is the smallest one not being used yet
     * @param name of the variable
     * @return the SatVar instance
     * @throws ExistingVariableException if the name chosen has already been used
     */
    public SatVar addVariable(String name) throws ExistingVariableException {
        return this.addVariable(name, this.variables.size() + 1);
    }

    /**
     * Gets a variable from the model using the id, or creates a new one
     * @return the SatVar instance with the asked id
     */
    private SatVar addOrGetVariable(Integer id) {
        Integer actualId = abs(id);
        if (this.variableNames.containsKey(actualId)) {
            String varName = this.variableNames.get(actualId);
            return this.variables.get(varName);
        } else {
            String varName = "var" + id.toString();
            String finalVarName = varName;

            try {
                return this.addVariable(finalVarName, id);
            } catch (ExistingVariableException e) {
                // will not happen with AlloyTools
                e.printStackTrace();
                return null;
            }
        }
    }

    /**
     * Add an Expr instance, which makes a constraint, to the list of constraint of the model
     */
    public void addConstraint(Expr expr) {
        this.constraints.add(expr);
    }

    /**
     * Add a new constraint, by translating a list of integers, as you could read in a cnf-modeled file (without 0)
     */
    public void addCnfClause(ArrayList<Integer> arrInt) throws InvalidClauseException {
        Expr expr = null;

        for (Integer id : arrInt) {
            if (id == 0) {
                throw new InvalidClauseException("Cannot have variable 0 in a cnf clause.");
            }

            Expr var = this.addOrGetVariable(id);

            if (id < 0) {
                var = var.negate();
            }

            if (expr == null) {
                expr = var;
            } else {
                expr = expr.or(var);
            }
        }

        this.constraints.add(expr);
    }

    /**
     * Add a new constraint, by translating an array of integers, as you could read in a cnf-modeled file (without 0)
     */
    public void addCnfClause(int[] arrInt) throws InvalidClauseException {
        ArrayList<Integer> arr = new ArrayList<>();
        for (int i : arrInt) {
            arr.add(i);
        }

        addCnfClause(arr);
    }

    /**
     * Add new constraints, by translating each list of integers from an array,
     * as you could read in a cnf-modeled file (without 0)
     */
    public void addListCnfClauses(ArrayList<ArrayList<Integer>> arrClauses) throws InvalidClauseException {
        for (ArrayList<Integer> clause : arrClauses) {
            this.addCnfClause(clause);
        }
    }

    /**
     * Add new constraints, by translating each list of integers from an array,
     * as you could read in a cnf-modeled file (without 0)
     */
    public void addListCnfClauses(int[][] arrClauses) throws InvalidClauseException {
        Expr expr = null;

        for (int[] clause : arrClauses) {
            this.addCnfClause(clause);
        }

        this.constraints.add(expr);
    }

    /**
     * Builds the string version of the problem, written in the CNF format
     * Ready to be saved or sent as .cnf file
     * @return returns the str value of the text
     * @throws UnsupportedOperationException
     */
    public String buildStrModel() throws UnsupportedOperationException {
        ArrayList<Expr> clauses = constraintsToClauses();

        // writes the first row
        StringBuilder strBuff = new StringBuilder()
                .append("p cnf ")
                .append(Integer.toString(variables.size())).append(" ")
                .append(Integer.toString(clauses.size())).append("\n");

        // writes the row for each clause
        for (Expr reducedClause : clauses) {
            strBuff.append(reducedClause.getCnfStr()).append("\n");
        }

        return strBuff.toString();
    }

    /**
     * Analyse the SEResults, containing the results returned from the solver, to complete the model
     * aka to set the values of the {@link #variables}
     * @param result
     */
    protected void processResults(Helper.SEResults result) {
        solveStatus = SolveStatusCode.build(result.status);

        for (Helper.SEVariable variable : result.variables) {
            int id = Integer.valueOf(variable.name);

            if (variableNames.containsKey(id)){
                String varName = variableNames.get(id);
                SatVar var = variables.get(varName);
                var.setValue((variable.value == 1));
            }
        }
    }

    /**
     * Prints a summary of the results
     */
    public void printResults() {
        ArrayList<String> arrLines = new ArrayList<>();
        arrLines.add("Status : " + this.solveStatus.getStrVal());

        for (SatVar var : this.variables.values()) {
            arrLines.add(var.getResult());
        }

        System.out.println(String.join("\n", arrLines));
    }

    /**
     * Remove a variable of the three hashmaps from the model, using its name
     * @param name
     */
    private void removeVariable(String name) {
        if (variables.containsKey(name)) {
            int id = variables.get(name).getId();
            variableNames.remove(id);
            variables.remove(name);
        }
    }

    /**
     * Remove a variable of the three hashmaps from the model, using its id
     * @param id
     */
    public void removeVariable(int id) {
        if (variableNames.containsKey(id)) {
            removeVariable(variableNames.get(id));
        }
    }
}

/**
 * An Expr is a either an alone variable,
 * a list of Variables linked by an operator,
 * or a list of Expr linked by an operator
 */
class Expr {
    String OPERATOR = "ERROR";

    @Override
    public String toString() {
        throw new UnsupportedOperationException();
    }

    public ListExpr convertToCnf() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    /**
     * The next methods produce a particular ListEpxr linking this instance and the input
     * @param other expression to be linked with
     * @return ListExpr of this and other
     */
    public OR or(Expr other){ return new OR(this, other); }

    public AND and(Expr other){ return new AND(this, other); }

    public XOR xor(Expr other){ return new XOR(this, other); }

    public IMP implies(Expr other){ return new IMP(this, other); }

    public EQ eq(Expr other){ return new EQ(this, other); }

    public NE ne(Expr other){ return new NE(this, other); }

    /**
     * Returns the negation of this
     */
    public Expr negate() { return new NEG(this); }

    /**
     * Subclass must have this method to make a cnf-modeled string of the expression
     * A variable will just return the string of its id, for example
     */
    public String getCnfStr() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    public String getOPERATOR() { return OPERATOR; }
}


class NEG extends Expr {
    private String OPERATOR = "-";
    private Expr inner;

    public NEG(Expr inner) {
        assert !(inner instanceof NEG) : "Input for NEG expression is of wrong instance";
        this.inner = inner;
    }

    @Override
    public String toString() {
        return this.OPERATOR + this.inner;
    }

    public Expr negate() {
        return this.inner;
    }

    public String getCnfStr() {
        // get the id of the variable or negation of a variable
        assert (this.inner instanceof SatVar) : "Input for NEG expression is of wrong instance 952";
        SatVar inner1 = (SatVar) this.inner;
        return this.OPERATOR + inner1.getId();
    }

    private Expr getInner() {
        return inner;
    }

    public ListExpr convertToCnf() throws UnsupportedOperationException {
        Expr expr = this.getInner();

        if (expr instanceof SatVar) {
            return new AND(new OR(this));
        }
        if (expr instanceof XOR) {
            expr = ((XOR) expr).getEquivalentExpr();
        } else if (expr instanceof IMP) {
            expr = ((IMP) expr).getEquivalentExpr();
        } else if (expr instanceof EQ) {
            expr = ((EQ) expr).getEquivalentExpr();
        } else if (expr instanceof NE) {
            expr = ((NE) expr).getEquivalentExpr();
        }

        if (expr instanceof AND) {
            ArrayList<Expr> l = new ArrayList<>();

            for (Expr expr1 : ((ListExpr) expr).getContent()) {
                l.add(expr1.negate());
            }

            return new OR(l).convertToCnf();
        }

        if (expr instanceof OR) {
            ArrayList<Expr> l = new ArrayList<>();

            for (Expr expr1 : ((ListExpr) expr).getContent()) {
                l.add(expr1.negate());
            }

            return new AND(l).convertToCnf();
        }

        throw new IllegalArgumentException("found not supported inner type " +
                this.inner);
    }
}

/**
 * An Expr is a set of one or several boolean variables being linked to each other
 * through different operators that can link booleans
 */
class ListExpr extends Expr {
    // a dummy expr class for expression which can contain multiple expressions
    private ArrayList<Expr> content;

    ListExpr(ArrayList<Expr> content) {
        this.content = new ArrayList<>();
        this.addOther(content);
    }

    ListExpr(Expr one, Expr other) {
        this(makeArray(one, other));
    }

    ListExpr(Expr content) {
        this(makeArray(content));
    }

    private static ArrayList<Expr> makeArray(Expr one, Expr other){
        ArrayList<Expr> arr = new ArrayList<>();
        arr.add(one);
        arr.add(other);
        return arr;
    }

    private static ArrayList<Expr> makeArray(Expr elem){
        ArrayList<Expr> arr = new ArrayList<>();
        arr.add(elem);
        return arr;
    }

    private void addOther(ArrayList<Expr> content) {
        for (Expr expr : content) {
            if (expr.getClass() == this.getClass()) {
                ListExpr e = (ListExpr) expr;
                this.getContent().addAll(e.getContent());
            } else {
                this.getContent().add(expr);
            }
        }
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toString() {
        StringBuffer buff = new StringBuffer()
                .append("(");
        for (Expr expr : this.getContent()) {
            buff.append(expr.toString());
            buff.append(" ");
            buff.append(this.getOPERATOR());
            buff.append(" ");
        }
        int toRemove = 1 + this.getOPERATOR().length() + 1;
        buff.delete(buff.length() - toRemove, buff.length())
                .append(")");
        return buff.toString();
    }

    public ArrayList<Expr> getContent() {
        return content;
    }

}


class AND extends ListExpr {
    // and expression
    String OPERATOR = "&";

    public AND(ArrayList<Expr> content) {
        super(content);
    }

    public AND(Expr one, Expr other) {
        super(one, other);
    }

    public AND(Expr elem) {
        super(elem);
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        ArrayList<Expr> l = new ArrayList<>();
        for (Expr expr : this.getContent()) {
            for (Expr expr1 : expr.convertToCnf().getContent()) {
                l.add(expr1);
            }
        }
        return new AND(l);
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }
}


class OR extends ListExpr {
    String OPERATOR ="|";

    public OR(ArrayList<Expr> content) {
        super(content);
    }

    public OR(Expr one, Expr other) {
        super(one, other);
    }

    public OR(Expr elem) {
        super(elem);
    }

    @Override
    public AND convertToCnf() throws UnsupportedOperationException {
        ArrayList<ArrayList<Expr>> l = new ArrayList<>();
        for (Expr expr : this.getContent()) {
            l.add(expr.convertToCnf().getContent());
        }


        ArrayList<ArrayList<Expr>> l1 = tools.iterProduct(l);

        ArrayList<Expr> l2 = new ArrayList<>();
        for (ArrayList<Expr> expr : l1) {
            l2.add(new OR(expr));
        }

        return new AND(l2);
    }

    @Override
    public String getCnfStr() throws UnsupportedOperationException {
        StringBuffer buff = new StringBuffer();
        for (Expr expr : this.getContent()) {
            buff.append(expr.getCnfStr());
            buff.append(" ");
        }
        buff.append("0");
        return buff.toString();
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }
}

/**
 * When the operator cannot link more than 2 Expressions, we use BinaryExpr instead of ListExpr
 */
class BinaryExpr extends Expr {
    /* Left expression */
    private Expr lhs;
    /* Right expression */
    private Expr rhs;

    public BinaryExpr(Expr lhs, Expr rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public Expr getLhs() {
        return lhs;
    }

    public Expr getRhs() {
        return rhs;
    }

    @Override
    public String toString() {
        return new StringBuffer()
                .append("(")
                .append(lhs)
                .append(" ")
                .append(this.getOPERATOR())
                .append(" ")
                .append(rhs)
                .append(")")
                .toString();
    }

    /**
     * get expression which only uses AND, OR and NEG and is equivalent
     */
    public ListExpr getEquivalentExpr() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }
}


class XOR extends BinaryExpr {
    // xor expression
    String OPERATOR = "^";

    public XOR(Expr lhs, Expr rhs) {
        super(lhs, rhs);
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        return this.getEquivalentExpr().convertToCnf();
    }

    /**
     * get expression which only uses AND, OR and NEG and is equivalent
     */
    public ListExpr getEquivalentExpr() {
        // (this.lhs & -this.rhs) | (-this.lhs & this.rhs)
        return this.getLhs().and(this.getRhs().negate()).or(this.getLhs().negate().and(this.getRhs()));
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }

}


class EQ extends BinaryExpr {
    // equivalence expression
    String OPERATOR = "==";

    public EQ(Expr lhs, Expr rhs) {
        super(lhs, rhs);
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        return this.getEquivalentExpr().convertToCnf();
    }

    /**
     * get expression which only uses AND, OR and NEG and is equivalent
     */
    public ListExpr getEquivalentExpr() {
        // (this.lhs & this.rhs) | (-this.lhs & -this.rhs)
        return this.getLhs().and(this.getRhs())
                .or(this.getLhs().negate().and(this.getRhs().negate()));
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }

}


class NE extends BinaryExpr {
    // non equal expression
    String OPERATOR = "!=";

    public NE(Expr lhs, Expr rhs) {
        super(lhs, rhs);
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        return this.getEquivalentExpr().convertToCnf();
    }

    /**
     * get expression which only uses AND, OR and NEG and is equivalent
     */
    public ListExpr getEquivalentExpr() {
        // (-this.lhs | -this.rhs) & (this.lhs | this.rhs)
        return (ListExpr) this.getLhs().negate().or(this.getRhs().negate())
                .and(this.getLhs().or(this.getRhs()));
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }

}


class IMP extends BinaryExpr {
    // implication expression
    String OPERATOR = "=>";

    public IMP(Expr lhs, Expr rhs) {
        super(lhs, rhs);
    }

    @Override
    public ListExpr convertToCnf() throws UnsupportedOperationException {
        return this.getEquivalentExpr().convertToCnf();
    }

    /**
     * get expression which only uses AND, OR and NEG and is equivalent
     */
    public ListExpr getEquivalentExpr() {
        // -this.lhs | this.rhs
        return (ListExpr) this.getLhs().negate().or(this.getRhs());
    }

    @Override
    public String getOPERATOR() { return OPERATOR; }
}


/**
 * Do the same thing as we expect from itertools.product in python
 * [[A, B], [C, D], [E]] will return [[A, C, E], [A, D, E], [B, C, E], [B, D, E]]
 */
class tools {
    public static ArrayList<ArrayList<Expr>> iterProduct(ArrayList<ArrayList<Expr>> input){
        ArrayList<ArrayList<Expr>> res = new ArrayList<>();
        ArrayList<Expr> temArray;
        ArrayList<Expr> temArray2;

        if (input.size() > 1) {
            ArrayList<Expr> firstArray = input.get(0);
            input.remove(0);

            ArrayList<ArrayList<Expr>> nextInput = iterProduct(input);

            for (Expr expr : firstArray) {
                temArray = new ArrayList<>();
                temArray.add(expr);

                for (ArrayList<Expr> exprs : nextInput) {
                    temArray2 = (ArrayList<Expr>) temArray.clone();
                    temArray2.addAll(exprs);
                    res.add(temArray2);
                }
            }
        } else {
            for (Expr expr : input.get(0)) {
                temArray = new ArrayList<>();
                temArray.add(expr);
                res.add(temArray);
            }
        }

        return res;
    }
}

