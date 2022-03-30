package org.alloytools.alloy.core.api;

import java.io.File;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.alloytools.alloy.core.api.Visualizer.Renderer;

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

    /**
     * Convenience to get a number of instances from a source
     *
     * @param source the soufce code
     * @param max the maximum nr of instances
     * @return an array of instances
     */
    default Instance[] getInstances(String source, int max) {
        return getSolution(source).next(max);
    }

    /**
     * Convenience method to get a solution from a source
     *
     * @param source the source code
     * @return the solution
     */
    default Solution getSolution(String source) {
        TModule module = getModule(source);
        Solver solver = getSolvers().get("");
        Solution solution = solver.solve(module.getDefaultCommand(), null);
        return solution;
    }

    /**
     * Convenience method to return a module
     *
     * @param source the source code
     * @return the module
     */
    default TModule getModule(String source) {
        return compiler().compileSource(source);
    }

    /**
     * The version of the Alloy environment
     *
     * @return the version
     */
    String getVersion();


    /**
     * Create a new object from the given class injection some domain objects like
     * Alloy in the constructor.
     *
     * @param <T> the type
     * @param type the class that needs to be instantiated
     * @return the new object
     */
    <T> T create(Class<T> type);

    /**
     * Find a renderer for the given domain object type & output type
     *
     * @param <A> the domain object type
     * @param <O> the output object type
     * @param glob the glob for the name
     * @param argument the agumen type
     * @param output the output type
     * @return the optional renderer
     */
    <A, O> Optional<Renderer<A,O>> findRenderer(String glob, Class<A> argument, Class<O> output);

    /**
     * Turn a plugin specific options object ( a data transfer object or DTO, i.e.
     * public fields) into an AlloyOptions
     *
     * @param <T> the domain options type
     * @param options the options DTO
     * @return an AlloyOptions object
     */
    <T> AlloyOptions<T> asOptions(T options);

}
