package kodkod.engine;

import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.Translation;

/**
 * A {@link Retargeter} describes a re-targeting strategy for target-oriented
 * model-finding. Once registered via {@link ExtendedOptions}, it will be called
 * by the underlying solver after every instance produced. For the default
 * behavior, which is followed when no Retargeter is registered, see the
 * private class DefaultRetargeter within {@link ExtendedSolver}.
 *
 * @author Tim Nelson
 */
public interface Retargeter {
    /**
     * The retarget method exposes the Translation, etc. to enable maximum
     * flexibility for the caller; an empty retargeting method will implement standard
     * enumeration (with no retargeting); the solver will always issue a new clause
     * to exclude repeat instances regardless of retargeting strategy.
     *
     * Note that the TargetSATSolver instance is transl.cnf()
     *       and the ExtendedOptions instance is transl.options()
     * @param transl The current boolean Translation (for retrieving primary variables, etc.)
     */
    void retarget(Translation transl);
}
