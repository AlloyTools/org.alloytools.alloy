package org.alloytools.alloy.lsp.provider;

import java.util.List;

import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.MessageType;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.Range;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.SymbolKind;

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