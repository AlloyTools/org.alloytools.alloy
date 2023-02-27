package org.alloytools.alloy.lsp.provider;

import java.util.List;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.Command;
import org.eclipse.lsp4j.jsonrpc.services.JsonNotification;
import org.eclipse.lsp4j.services.LanguageClient;

public interface AlloyLanguageClient extends LanguageClient {
	@JsonNotification("alloy/showExecutionOutput")
	CompletableFuture<?> showExecutionOutput(AlloyLSMessage params);

	@JsonNotification("alloy/commandsListResult")
	CompletableFuture<?> commandsListResult(CommandsListResult commands);

	public class CommandsListResult{
		public List<CommandsListResultItem> commands;

		public CommandsListResult(List<CommandsListResultItem> commands) {
			this.commands = commands;
		}

	}
	public class CommandsListResultItem{
		public String title;
		public Command command;

		public CommandsListResultItem(String title, Command command) {
			this.title = title;
			this.command = command;
		}

	}
}
