package org.alloytools.alloy.classic.solver.kodkod;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.alloytools.alloy.classic.provider.AlloyModuleClassic;
import org.alloytools.alloy.classic.provider.Atom;
import org.alloytools.alloy.classic.provider.Relation;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.alloy.core.api.TFunction.Parameter;
import org.alloytools.alloy.core.api.TSignature;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;


class InstanceImpl implements Instance {


    final A4Solution         ai;
    final CompModule         orig;
    final TSignature         univ;
    final SolutionImpl       solution;
    final int                state;
    final Map<String,Object> variables = new TreeMap<>();

    InstanceImpl(SolutionImpl solution, A4Solution ai, int state) {
        this.solution = solution;
        this.ai = ai;
        this.state = state;
        this.orig = ((AlloyModuleClassic) solution.module).getOriginalModule();
        this.univ = solution.module.getSignatures().get("univ");
    }

    @Override
    public IRelation getField(TField field) {
        A4TupleSet eval = ai.eval((Field) field, state);

        return to(eval);
    }

    @Override
    public IRelation getAtoms(TSignature sig) {
        A4TupleSet set = ai.eval((Sig) sig, state);

        return to(set);
    }

    @Override
    public Map<String,Object> getVariables() {
        if (variables.isEmpty()) {
            for (ExprVar skolem : ai.getAllSkolems()) {
                Object eval = eval(skolem);
                variables.put(skolem.label, eval);
            }
        }
        return variables;
    }

    @Override
    public IRelation getVariable(String fun, String var) {
        String name = "$" + solution.command.getName() + "_" + var;
        for (ExprVar skolem : ai.getAllSkolems()) {
            if (skolem.label.equals(name)) {
                A4TupleSet set = (A4TupleSet) ai.eval(skolem, state);
                return to(set);
            }
        }
        return null;
    }

    @Override
    public IRelation eval(String cmd) {
        try {
            Expr expr = orig.parseOneExpressionFromString(cmd);
            return eval(expr);
        } catch (Err | IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    private IRelation eval(Expr expr) {
        Object eval = ai.eval(expr, state);
        if (expr.getType().contains(Sig.SIGINT)) {
            if (eval instanceof String) {
                String nr = (String) eval;
                Atom atom = solution.createAtom((String) eval, Sig.SIGINT);
                return new Relation(solution, atom);
            }
        }
        if (eval instanceof A4TupleSet) {
            return to((A4TupleSet) eval);
        }
        if (eval instanceof Boolean) {
            Boolean b = (Boolean) eval;
            if (b) {
                return solution.true_;
            } else
                return solution.false_;
        }
        // TODO log
        System.out.println("unknown type from eval " + eval);
        throw null;
    }

    @Override
    public String toString() {
        return "Instance[state=" + state + "]";
    }

    Relation to(A4TupleSet set) {
        List<IAtom> atoms = new ArrayList<>();

        for (A4Tuple tuple : set) {
            for (int j = 0; j < set.arity(); j++) {
                String atomName = tuple.atom(j);
                TSignature sig = tuple.sig(j);
                //
                // A4 gives us the positive first
                // integers with type "seq/Int". Not
                // sure I understand why and it eats the
                // symbols for integers. We create a
                // special atom for the seq (not sure when
                // and where it is needed) and then create
                // the integer symbol.
                //

                if (sig.getName().startsWith("seq/Int")) {
                    solution.createAtom("[" + atomName + "]", sig);
                    sig = solution.module.getSignatures().get("Int");
                }
                Atom atom = solution.createAtom(atomName, sig);
                atoms.add(atom);
            }
        }

        return new Relation(solution, set.arity(), atoms);
    }

    @Override
    public Map<String,IRelation> getParameters(TFunction foo) {
        Map<String,IRelation> parameters = new HashMap<>();
        String prefix = "$" + foo.getName() + "_";
        for (Parameter parameter : foo.getParameters()) {
            IRelation value = getVariable(foo.getName(), parameter.getName());
            parameters.put(parameter.getName(), value);
        }
        return parameters;
    }

    @Override
    public Map<TField,IRelation> getObject(IAtom atom) {
        TSignature sig = atom.getSig();
        Map<TField,IRelation> result = new HashMap<>();
        for (Map.Entry<String,TField> e : sig.getFieldMap().entrySet()) {
            TField f = e.getValue();
            IRelation allData = getField(f);
            IRelation objectData = allData.select(atom);
            result.put(f, objectData);
        }
        return result;
    }

}
