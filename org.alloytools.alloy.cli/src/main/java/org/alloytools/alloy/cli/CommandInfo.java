package org.alloytools.alloy.cli;

import edu.mit.csail.sdg.ast.Command;

public class CommandInfo implements Comparable<CommandInfo>{
	public Command command;
	public long durationInMs;
	@Override
	public int compareTo(CommandInfo o) {
		return command.label.compareTo(o.command.label);
	}
}
