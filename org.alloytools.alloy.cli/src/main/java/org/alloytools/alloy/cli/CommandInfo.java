package org.alloytools.alloy.cli;

import java.io.File;

import edu.mit.csail.sdg.ast.Command;

public class CommandInfo implements Comparable<CommandInfo>{
	public Command command;
	public long durationInMs;
	public File cnf;
	public File kodkod;
	@Override
	public int compareTo(CommandInfo o) {
		return command.label.compareTo(o.command.label);
	}
}
