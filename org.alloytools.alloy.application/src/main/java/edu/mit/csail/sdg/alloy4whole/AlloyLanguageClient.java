package edu.mit.csail.sdg.alloy4whole;

import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.ApplyWorkspaceEditParams;
import org.eclipse.lsp4j.ApplyWorkspaceEditResponse;
import org.eclipse.lsp4j.MessageParams;
import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.services.LanguageClient;

public interface AlloyLanguageClient extends LanguageClient {
	@JsonNotification("alloy/showExecutionOutput")
	CompletableFuture<?> showExecutionOutput(AlloyLSMessage params);
}
