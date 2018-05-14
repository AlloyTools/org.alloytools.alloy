package org.alloytools.alloy.core.api;

public interface CompilerMessage {
	String getMessage();
	String getSource();
	String getPath();
	int line();
	int column();
	
	
}
