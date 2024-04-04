package org.alloytools.alloy.cli;

import java.io.File;

import edu.mit.csail.sdg.ast.Command;

public class CommandInfo implements Comparable<CommandInfo>{
	public Command command;
	public long durationInMs;
	public File cnf;
	public File kodkod;
	public int trace;
	@Override
	public int compareTo(CommandInfo o) {
		int n = command.label.compareTo(o.command.label);
		if ( n != 0)
			return n;
		return Integer.compare(trace, o.trace);
	}
}
