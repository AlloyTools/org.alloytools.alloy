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

	public static MessageParams newMessageParams(String message, MessageType type) {
		MessageParams res = new MessageParams();
		res.setMessage(message);
		res.setType(type);
		return res;
	}

	public static Location newLocation(Range range, String uri) {
		Location location = new Location();
		location.setRange(range);
		location.setUri(uri);
		return location;
	}

	public static SymbolInformation newSymbolInformation(String name, Location location, SymbolKind kind) {
		SymbolInformation symbolInfo = new SymbolInformation();
		symbolInfo.setLocation(location);
		symbolInfo.setName(name);
		symbolInfo.setKind(kind);
		return symbolInfo;
	}


	public static int positionCompare(Position p1, Position p2){	
		return p1.getLine() < p2.getLine() ? -1 : p1.getLine() > p2.getLine() ? 1 :
			   p1.getCharacter() < p2.getCharacter() ? -1 :
			   p1.getCharacter() > p2.getCharacter() ? 1 :
			   0;
	}
}
