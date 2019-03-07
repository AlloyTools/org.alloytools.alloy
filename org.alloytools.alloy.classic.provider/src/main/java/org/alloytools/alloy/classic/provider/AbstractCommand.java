package org.alloytools.alloy.classic.provider;

import java.util.Set;

import org.alloytools.alloy.core.api.Module;
import org.alloytools.alloy.core.api.TCheck;
import org.alloytools.alloy.core.api.TCommand;
import org.alloytools.alloy.core.api.TRun;
import org.alloytools.alloy.core.api.TScope;

import edu.mit.csail.sdg.ast.Command;

public class AbstractCommand implements TCommand, TRun, TCheck {
	final Command command;
	final Module	module;

	AbstractCommand(Module module, Command command) {
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
	public Module getModule() {
		return module;
	}

	public Command getOriginalCommand() {
		return command;
	}


}
