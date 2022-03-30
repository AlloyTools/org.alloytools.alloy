package org.alloytools.alloy.classic.provider;

import java.util.Set;

import org.alloytools.alloy.core.api.TModule;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TExpression;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TScope;

import edu.mit.csail.sdg.ast.Command;

public class AbstractCommand implements TCommand, TRun, TCheck {

    final Command command;
    final TModule  module;

    AbstractCommand(TModule module, Command command) {
        this.module = module;
        this.command = command;
    }

    @Override
    public String getName() {
        return command.getName();
    }

    @Override
    public Set<TScope> getScopes() {
        return command.getScopes();
    }

    @Override
    public Expects getExpects() {
        return command.getExpects();
    }

    @Override
    public TModule getModule() {
        return module;
    }

    public Command getOriginalCommand() {
        return command;
    }

    @Override
    public String toString() {
        return command.label + " " + command.nameExpr;
    }

    @Override
    public TExpression getExpression() {
        return command.getExpression();
    }

    @Override
    public boolean isCheck() {
        return command.isCheck();
    }


}
