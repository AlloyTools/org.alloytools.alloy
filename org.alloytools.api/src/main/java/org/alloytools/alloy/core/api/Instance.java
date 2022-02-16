package org.alloytools.alloy.core.api;

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

/**
 * Represents a value assignment that satisfies an Alloy specification. An
 * instance belongs to a {@link Solution}. A solution can have multiple
 * instances, all satisfying the same Alloy specification.
 * <p>
 * An instance represents the <em>state</em> of a model. Each satisfied
 * {@link Solution} provides a set of {@link Instance} objects where the static
 * aspects of the model can vary.
 * <p>
 * If a model has variables, then the instance represents the root of a time
 * <em>trace</em>. A trace is a set of instances representing a possible state
 * of the model in time. The API provides methods to navigate through the static
 * state of the model (a.k.a. configurations) and the state of the variables of
 * the model (a.k.a. traces).
 *
 */
public interface Instance {

    /**
     * Get the value of a field
     *
     * @param field the field
     * @return the values
     */
    IRelation getField(TField field);

    /**
     * Get the valueof a sig.
     *
     * @param sig the sig
     * @return the atoms with an arity=1
     */
    IRelation getAtoms(TSignature sig);

    /**
     * Get the value of a variable from a function.
     *
     * @param functionName the function name
     * @param varName the variable name
     * @return the value (can be empty)
     */
    IRelation getVariable(String functionName, String varName);

    /**
     * Evaluate an expression in the context of this instance. TODO what is the
     * syntax?
     *
     * @param expr the expression to evaluate.
     * @return the return value.
     */

    IRelation eval(String expr);



    default IRelation univ() {
        return eval("univ");
    }

    default IRelation iden() {
        return eval("iden");
    }

    static Instance empty() {
        return new Instance() {

            @Override
            public IRelation getField(TField field) {
                return null;
            }

            @Override
            public IRelation getAtoms(TSignature sig) {
                return null;
            }

            @Override
            public IRelation getVariable(String functionName, String varName) {
                return null;
            }

            @Override
            public IRelation eval(String expr) {
                return null;
            }

            @Override
            public Map<String,Object> getVariables() {
                return Collections.emptyMap();
            }

            @Override
            public Map<String,IRelation> getParameters(TFunction foo) {
                return Collections.emptyMap();
            }

            @Override
            public Map<TField,IRelation> getObject(IAtom atom) {
                return Collections.emptyMap();
            }
        };
    }

    Map<String,Object> getVariables();



    @SuppressWarnings({
                       "unchecked", "rawtypes"
    } )
    static Instance[] sort(Instance[] instances, String sortBy) {
        Instance[] clone = instances.clone();
        Arrays.sort(clone, (a, b) -> {
            Comparable aa = null;
            Comparable bb = null;
            try {
                aa = (Comparable) a.eval(sortBy);
                bb = (Comparable) b.eval(sortBy);
                if (aa == bb)
                    return 0;
                if (aa == null)
                    return -1;
                if (bb == null)
                    return 1;
                return aa.compareTo(bb);
            } catch (Exception e) {
                System.out.println(aa + " <> " + bb + " " + e);
                return 0;
            }
        });
        return clone;
    }

    Map<String,IRelation> getParameters(TFunction foo);

    Map<TField,IRelation> getObject(IAtom atom);
}
