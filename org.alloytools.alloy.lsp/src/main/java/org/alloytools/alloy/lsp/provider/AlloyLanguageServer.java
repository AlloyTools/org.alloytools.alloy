package org.alloytools.alloy.lsp.provider;

import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.fileUriToPath;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Future;

import org.eclipse.lsp4j.CodeLensOptions;
import org.eclipse.lsp4j.DocumentLinkOptions;
import org.eclipse.lsp4j.InitializeParams;
import org.eclipse.lsp4j.InitializeResult;
import org.eclipse.lsp4j.ServerCapabilities;
import org.eclipse.lsp4j.TextDocumentSyncKind;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.launch.LSPLauncher;
import org.eclipse.lsp4j.launch.LSPLauncher.Builder;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.LanguageServer;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;

public class AlloyLanguageServer implements LanguageServer, LanguageClientAware {

    private AlloyLanguageClient      client;
    private AlloyTextDocumentService alloyTextDocumentService;

    @Override
    public CompletableFuture<InitializeResult> initialize(InitializeParams params) {

        service().directory = params.getRootUri() != null ? fileUriToPath(params.getRootUri()) : null;

        InitializeResult res = new InitializeResult();
        ServerCapabilities caps = new ServerCapabilities();

        caps.setTextDocumentSync(Either.forLeft(TextDocumentSyncKind.Full));

        caps.setDefinitionProvider(true);
        caps.setHoverProvider(true);
        caps.setCodeLensProvider(new CodeLensOptions());
        caps.setDocumentLinkProvider(new DocumentLinkOptions());
        caps.setReferencesProvider(true);
        caps.setRenameProvider(true);
        //caps.setDocumentHighlightProvider(true);
        caps.setWorkspaceSymbolProvider(true);
        caps.setDocumentSymbolProvider(true);

        res.setCapabilities(caps);
        return CompletableFuture.completedFuture(res);
    }

    @Override
    public CompletableFuture<Object> shutdown() {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public void exit() {
        System.exit(0);
    }

    @Override
    public TextDocumentService getTextDocumentService() {
        return service();
    }

    private AlloyTextDocumentService service() {
        if (alloyTextDocumentService == null)
            alloyTextDocumentService = new AlloyTextDocumentService(client);
        return alloyTextDocumentService;
    }

    @Override
    public WorkspaceService getWorkspaceService() {
        return service();
    }



    // LanguageClientAware
    @Override
    public void connect(LanguageClient client) {
        System.err.println("AlloyLanguageServer.connect() called");
        this.client = (AlloyLanguageClient) client;

        if (this.alloyTextDocumentService != null) {
            this.alloyTextDocumentService.connect(this.client);
        }

    }

    public static void main(String[] args) throws Exception {
        if (args.length == 2) {
            int port = Integer.parseInt(args[1]);
            InputStream inputStream;
            OutputStream outputStream;
            AlloyLanguageServer langserv = new AlloyLanguageServer();
            try (java.net.Socket socket = new Socket("localhost", port)) {
                inputStream = socket.getInputStream();
                outputStream = socket.getOutputStream();
                System.err.println("connected!");
                Launcher<AlloyLanguageClient> launcher = createServerLauncher(langserv, AlloyLanguageClient.class, inputStream, outputStream);
                System.err.println("Starting Alloy Language Server!");
                langserv.connect(launcher.getRemoteProxy());
                Future<Void> res = launcher.startListening();
                System.err.println("Alloy Language Server Started!");
                res.get();
                System.err.println("########Exited Alloy Language Server!");
            }
        } else {
            AlloyLanguageServer server = new AlloyLanguageServer();
            Launcher<LanguageClient> l = LSPLauncher.createServerLauncher(server, System.in, System.out);
            server.connect(l.getRemoteProxy());
            Future< ? > startListening = l.startListening();
            startListening.get();
        }
    }

    /**
     * Create a new Launcher for a language server and an input and output stream.
     *
     * @param server - the server that receives method calls from the remote client
     * @param in - input stream to listen for incoming messages
     * @param out - output stream to send outgoing messages
     */
    public static <TLangClient extends LanguageClient> Launcher<TLangClient> createServerLauncher(LanguageServer server, Class< ? extends TLangClient> clientType, InputStream in, OutputStream out) {
        return new Builder<TLangClient>().setLocalService(server).setRemoteInterface(clientType).setInput(in).setOutput(out).create();
    }
}


