package org.alloytools.alloy.core.api;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Represents an Alloy Module
 */
public interface TModule {

    /**
     * The source path of this module. In certain cases a module does not have a
     * path, for example when it is compiled from a string.
     *
     * @return an optional file path to a module
     */
    Optional<String> getPath();

    /**
     * Get the defined sigs in this module
     *
     * @return a list of sigs
     */
    Map<String,TSignature> getSignatures();

    /**
     * Get any run commands defined in the module
     *
     * @return the list of available run commands
     */
    Map<String,TRun> getRuns();

    /**
     * Get any check commands defined in the module
     *
     * @return the list of available check commands
     */
    Map<String,TCheck> getChecks();

    /**
     * Get any check commands defined in the module
     *
     * @return the list of available check commands
     */
    Map<String,TExpression> getFacts();

    /**
     * Get any check commands defined in the module
     *
     * @return the list of available check commands
     */
    Set<TFunction> getFunctions();


    /**
     * Get compiler warnings.
     *
     * @return compiler warnings
     */
    List<CompilerMessage> getWarnings();

    /**
     * Get fatal compiler errors
     *
     * @return compiler errors
     */
    List<CompilerMessage> getErrors();

    /**
     * Return true if this module has no fatal errors.
     *
     * @return true if no fatal errors
     */
    boolean isValid();

    /**
     * Get the options in the source for the given command. A source option is
     * specified with {@code--option[suffix] option}. The suffix is by default
     * {@code *} which implies all.
     *
     * @param command
     * @return Options given in the source for the given command
     */
    Map<String,String> getSourceOptions(TCommand command);

    /**
     * Return the compiler that compiled this module.
     *
     * @return the compiler
     */
    Compiler getCompiler();

    /**
     * Get the defauklt command. This is the first command specified or the system
     * default.
     */
    default TCommand getDefaultCommand() {
        return getRuns().values().iterator().next();
    }

    /**
     * Get the lost of modules that this module has opened (open ..)
     */
    List<TOpen> getOpens();

    Optional<TFunction> getFunction(String name, int arity);

    Optional<TFunction> getFunction(String name);

}
