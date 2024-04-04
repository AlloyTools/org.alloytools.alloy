package org.alloytools.alloy.cli;

import java.io.IOException;
import java.io.PrintStream;
import java.io.Writer;

public class OutputTrace {
	final Appendable writer;

	public OutputTrace(Appendable writer) {
		this.writer = writer;
	}

	public OutputTrace format(String format, Object... args) throws IOException {
		if (writer != null) {
			writer.append(String.format(format, args));
			if (writer instanceof Writer) {
				((Writer) writer).flush();
			} else if (writer instanceof PrintStream) {
				((PrintStream) writer).flush();
			}
		}
		return this;
	}

	public OutputTrace back(int i) throws IOException {
		if (writer != null) {

			while (i-- > 0)
				this.writer.append('\u0008');

		}
		return this;
	}

}
