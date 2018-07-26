package edu.mit.csail.sdg.alloy4whole;

import java.util.Arrays;
import java.util.List;

import org.eclipse.lsp4j.*;

public class Lsp4jUtil {
	public static PublishDiagnosticsParams newPublishDiagnosticsParams(String uri, List<Diagnostic> diagnostics) {
		PublishDiagnosticsParams diagnosticsParams = new PublishDiagnosticsParams();
		diagnosticsParams.setDiagnostics(diagnostics);
		diagnosticsParams.setUri(uri);
		return diagnosticsParams;
	}
	
	public static Diagnostic newDiagnostic(String message, Range range) {
		Diagnostic res = new Diagnostic();
		res.setMessage(message);
		res.setRange(range);
		return res;
	}

}
