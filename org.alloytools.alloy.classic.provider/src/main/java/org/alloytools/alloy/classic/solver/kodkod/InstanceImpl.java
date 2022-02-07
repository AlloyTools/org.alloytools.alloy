package org.alloytools.alloy.classic.solver.kodkod;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.alloytools.alloy.classic.provider.AlloyModuleClassic;
import org.alloytools.alloy.classic.provider.Atom;
import org.alloytools.alloy.classic.provider.Relation;
import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.Instance;
import org.alloytools.alloy.core.api.TField;
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


    final A4Solution   ai;
    final CompModule   orig;
    final TSignature   univ;
    final SolutionImpl solution;
    final int          state;

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
    public Object eval(String cmd) {
        try {
            Expr expr = orig.parseOneExpressionFromString(cmd);
            Object eval = ai.eval(expr, state);
            if (eval instanceof A4TupleSet) {
                return to((A4TupleSet) eval);
            }
            if (eval instanceof Boolean) {
                return eval;
            }
            if (expr.getType().contains(Sig.SIGINT)) {
                String nr = (String) eval;
                return Integer.parseInt(nr);
            }
        } catch (Err | IOException e) {
            e.printStackTrace();
        }
        return null;
    }

    @Override
    public Relation universe() {
        A4TupleSet eval = ai.eval((Sig) univ, state);
        return to(eval);
    }

    @Override
    public IRelation ident() {
        return universe().toIdent();
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
                    createAtom("[" + atomName + "]", sig);
                    sig = solution.module.getSignatures().get("Int");
                }
                Atom atom = createAtom(atomName, sig);
                atoms.add(atom);
            }
        }

        return new Relation(solution, set.arity(), atoms);
    }

    Atom createAtom(String o, TSignature sig) {
        return solution.atoms.computeIfAbsent(o, k -> {
            return new Atom(solution, sig, o, o);
        });
    }


}
