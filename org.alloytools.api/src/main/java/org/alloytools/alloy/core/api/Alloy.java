package org.alloytools.alloy.core.api;

import java.io.File;
import java.util.List;
import java.util.Map;

/**
 * Primary interface into Alloy. An instance can be found through the Java
 * {@link java.util.ServiceLoader}
 * <p>
 * This class is the root into Alloy. It provides access to the solvers, the
 * compiler, and the visualizers.
 */
public interface Alloy {

    /**
     * Get a list of available solvers
     *
     * @return a list of available solvers
     */
    Map<String,Solver> getSolvers();

    /**
     * Return the compiler given a resolver for abstracting where the content is
     * coming from.
     *
     * @param resolver abstracts the file system
     * @return an Alloy compiler
     */
    Compiler compiler(SourceResolver resolver);

    /**
     * Return a list of visualizers that can render an {@link Instance}
     *
     * @return a list of visualizers
     */
    List<Visualizer> getVisualizers();

    /**
     * Return a default compiler based on the current file system
     *
     * @return a compiler
     */
    Compiler compiler();

    /**
     * Get a file in the Alloy private directory. The intention for this path is to
     * be used by solvers or visualizers for caches and preferences.
     *
     * @param pathWithSlashes a path separated with slashes also on windows
     * @return a Path to a file on the file system using slashes to separate
     *         directories.
     */
    File getPreferencesDir(String id);

    default Instance[] getInstances(String source, int max) {
        return getSolution(source).next(max);
    }

    default Solution getSolution(String source) {
        Module module = compiler().compileSource(source);
        Solver solver = getSolvers().get("");
        Solution solution = solver.solve(module.getDefaultCommand(), null);
        return solution;
    }

    String getVersion();
}
