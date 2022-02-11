package org.alloytools.alloy.classic.provider;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.alloytools.alloy.core.api.Compiler;
import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TExpression;
import org.alloytools.alloy.core.api.TFunction;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TSignature;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;

public class AlloyModuleClassic implements Module {

    final CompModule            module;
    final Compiler              compiler;
    final String                path;
    final List<CompilerMessage> errors   = new ArrayList<>();
    final List<CompilerMessage> warnings = new ArrayList<>();
    final List<Option>          options  = new ArrayList<>();
    final String                source;

    public AlloyModuleClassic(CompModule module, String path, String source, Compiler compiler, List<Option> options) {
        this.module = module;
        this.path = path;
        this.source = source;
        this.compiler = compiler;
        this.options.addAll(options);
    }

    public CompModule getOriginalModule() {
        return module;
    }

    @Override
    public Map<String,TSignature> getSignatures() {
        check();
        ConstList<Sig> sigs = module.getAllReachableSigs();

        Map<String,TSignature> all = sigs.stream().collect(Collectors.toMap(sk -> sk.label, sv -> sv));
        module.getAllSigs().forEach(sig -> {
            all.put(sig.label.substring("this/".length()), sig);
        });
        return all;
    }

    @Override
    public Map<String,TRun> getRuns() {
        check();
        Map<String,TRun> result = new LinkedHashMap<>();
        module.getAllCommands().stream().filter(c -> !c.isCheck()).map(r -> (TRun) new AbstractCommand(this, r)).forEach(e -> {
            result.put(e.getName(), e);
        });
        assert !result.isEmpty() : "If no commands are present we add a default command";
        return result;
    }

    @Override
    public Map<String,TCheck> getChecks() {
        check();
        return module.getAllCommands().stream().filter(c -> c.isCheck()).map(r -> (TCheck) new AbstractCommand(this, r)).collect(Collectors.toMap(kc -> kc.getName(), vc -> vc));
    }

    @Override
    public Map<String,TExpression> getFacts() {
        check();
        return module.getAllFacts().toList().stream().collect(Collectors.toMap(pk -> pk.a, pv -> pv.b));
    }

    @Override
    public Map<String,TFunction> getFunctions() {
        check();
        return module.getAllFunc().toList().stream().collect(Collectors.toMap(pk -> pk.label.substring("this/".length()), pv -> pv));
    }



    @Override
    public Optional<String> getPath() {
        check();
        return Optional.ofNullable(path);
    }

    @Override
    public List<CompilerMessage> getWarnings() {
        return warnings;
    }

    @Override
    public List<CompilerMessage> getErrors() {
        return errors;
    }

    @Override
    public boolean isValid() {
        return module != null && getErrors().isEmpty();
    }

    @Override
    public String toString() {
        if (module == null)
            return "invalid module on path " + path;
        else
            return module.toString();
    }

    @Override
    public Map<String,String> getSourceOptions(TCommand command) {
        return extractOptions(options, command);
    }

    @Override
    public Compiler getCompiler() {
        check();
        return compiler;
    }

    private void check() {
        if (module == null)
            throw new IllegalStateException("module could not compile: " + errors);
    }

    @Override
    public List<Module> getOpens() {
        return null;
    }

    private Map<String,String> extractOptions(List<Option> options, TCommand command) {
        String name = command.getName();
        return options.stream().filter(opt -> opt.glob.matcher(name).matches()).sorted().distinct().collect(Collectors.toMap(option -> option.key, option -> option.value));
    }
}
