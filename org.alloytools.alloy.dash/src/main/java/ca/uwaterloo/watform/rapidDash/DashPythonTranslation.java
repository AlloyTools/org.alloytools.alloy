package ca.uwaterloo.watform.rapidDash;

import ca.uwaterloo.watform.parser.DashModule;
import edu.mit.csail.sdg.ast.Sig;

import java.util.*;
import java.util.stream.Collectors;

import static edu.mit.csail.sdg.alloy4.TableView.clean;

/**
 * Mutable; this class represents an Dash to Python translation module
 */

public class DashPythonTranslation {

    private DashModule dashModule;

    public List<String> basicSigLabels;

    /**
     * Constructs a new DashPythonTranslation object
     *
     * @param dashModule - the DashModule we want to translate
     */
    public DashPythonTranslation(DashModule dashModule) {
        this.dashModule = dashModule;
        this.basicSigLabels = dashModule.sigs.values().stream()
                .filter(this::isSubSig)
                .map(sig -> clean(sig.label)).collect(Collectors.toList());
    }

    private Boolean isSubSig(Sig sig) {
        return sig.isSubsig != null & sig.isOne == null & sig.isAbstract == null & sig.isEnum == null &
                sig.isLone == null & sig.isMeta == null & sig.isPrivate == null & sig.isSome == null & sig.isSubset == null &
                sig.isVariable == null;
    }
}
