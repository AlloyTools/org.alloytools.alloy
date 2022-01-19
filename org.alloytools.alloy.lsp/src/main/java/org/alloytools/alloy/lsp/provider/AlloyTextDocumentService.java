package org.alloytools.alloy.lsp.provider;

import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreGranularity;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreMinimization;
import static edu.mit.csail.sdg.alloy4.A4Preferences.ImplicitThis;
import static edu.mit.csail.sdg.alloy4.A4Preferences.InferPartialInstance;
import static edu.mit.csail.sdg.alloy4.A4Preferences.NoOverflow;
import static edu.mit.csail.sdg.alloy4.A4Preferences.RecordKodkod;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SkolemDepth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Solver;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubMemory;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubStack;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Unrolls;
import static edu.mit.csail.sdg.alloy4.A4Preferences.VerbosityPref;
import static edu.mit.csail.sdg.alloy4.A4Preferences.WarningNonfatal;
import static org.alloytools.alloy.lsp.provider.AlloyLSMessageType.RunCompleted;
import static org.alloytools.alloy.lsp.provider.AlloyLSMessageType.RunResult;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.createRange;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.createRangeFromPos;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.filePathResolved;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.filePathToUri;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.fileUriToPath;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.fs;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.getResult;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.posToLocation;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.posToPosition;
import static org.alloytools.alloy.lsp.provider.AlloyLanguageServerUtil.positionToPos;
import static org.alloytools.alloy.lsp.provider.Lsp4jUtil.newDiagnostic;
import static org.alloytools.alloy.lsp.provider.Lsp4jUtil.newMessageParams;
import static org.alloytools.alloy.lsp.provider.Lsp4jUtil.newPublishDiagnosticsParams;
import static org.alloytools.alloy.lsp.provider.Lsp4jUtil.newSymbolInformation;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.alloytools.alloy.core.AlloyCore;
import org.alloytools.alloy.lsp.provider.AlloyLanguageClient.CommandsListResult;
import org.alloytools.alloy.lsp.provider.AlloyLanguageClient.CommandsListResultItem;
import org.apache.commons.io.FilenameUtils;
import org.eclipse.core.runtime.URIUtil;
import org.eclipse.lsp4j.CodeActionParams;
import org.eclipse.lsp4j.CodeLens;
import org.eclipse.lsp4j.CodeLensParams;
import org.eclipse.lsp4j.Command;
import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionList;
import org.eclipse.lsp4j.CompletionParams;
import org.eclipse.lsp4j.Diagnostic;
import org.eclipse.lsp4j.DiagnosticSeverity;
import org.eclipse.lsp4j.DidChangeConfigurationParams;
import org.eclipse.lsp4j.DidChangeTextDocumentParams;
import org.eclipse.lsp4j.DidChangeWatchedFilesParams;
import org.eclipse.lsp4j.DidCloseTextDocumentParams;
import org.eclipse.lsp4j.DidOpenTextDocumentParams;
import org.eclipse.lsp4j.DidSaveTextDocumentParams;
import org.eclipse.lsp4j.DocumentFormattingParams;
import org.eclipse.lsp4j.DocumentHighlight;
import org.eclipse.lsp4j.DocumentHighlightKind;
import org.eclipse.lsp4j.DocumentLink;
import org.eclipse.lsp4j.DocumentLinkParams;
import org.eclipse.lsp4j.DocumentOnTypeFormattingParams;
import org.eclipse.lsp4j.DocumentRangeFormattingParams;
import org.eclipse.lsp4j.DocumentSymbolParams;
import org.eclipse.lsp4j.Hover;
import org.eclipse.lsp4j.Location;
import org.eclipse.lsp4j.MarkupContent;
import org.eclipse.lsp4j.MessageType;
import org.eclipse.lsp4j.Position;
import org.eclipse.lsp4j.PublishDiagnosticsParams;
import org.eclipse.lsp4j.ReferenceParams;
import org.eclipse.lsp4j.RenameParams;
import org.eclipse.lsp4j.SignatureHelp;
import org.eclipse.lsp4j.SymbolInformation;
import org.eclipse.lsp4j.SymbolKind;
import org.eclipse.lsp4j.TextDocumentPositionParams;
import org.eclipse.lsp4j.TextEdit;
import org.eclipse.lsp4j.WorkspaceEdit;
import org.eclipse.lsp4j.WorkspaceSymbolParams;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.eclipse.lsp4j.services.LanguageClient;
import org.eclipse.lsp4j.services.LanguageClientAware;
import org.eclipse.lsp4j.services.TextDocumentService;
import org.eclipse.lsp4j.services.WorkspaceService;

import com.google.gson.Gson;
import com.google.gson.JsonPrimitive;

import edu.mit.csail.sdg.alloy4.A4Preferences.Verbosity;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Computer;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.WorkerEngine;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.alloy4whole.SimpleGUI;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleTask1;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleTask2;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Clause;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBad;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.VisitQueryOnce;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.parser.Macro;
import edu.mit.csail.sdg.sim.SimInstance;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;

class AlloyTextDocumentService implements TextDocumentService, WorkspaceService, LanguageClientAware {

    public AlloyLanguageClient client;
    public String              directory;
    private int                subMemoryNow;
    private int                subStackNow;

    public AlloyTextDocumentService(AlloyLanguageClient client) {
        this.client = client;
    }

    // LanguageClientAware
    @Override
    public void connect(LanguageClient client) {
        log("AlloyTextDocumentService.connect() called");
        this.client = (AlloyLanguageClient) client;
    }

    @Override
    public CompletableFuture<Either<List<CompletionItem>,CompletionList>> completion(CompletionParams position) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<CompletionItem> resolveCompletionItem(CompletionItem unresolved) {
        return CompletableFuture.completedFuture(unresolved);
    }

    Either<CompModule,Err> cachedCompModuleForFileUri     = null;

    /**
     * the file uri of the cached module. If this is not null, the cached module is
     * valid for the uri
     */
    String                 cachedCompModuleForFileUri_Uri = null;

    CompModule getCompModuleForFileUri(String uri) {
        // log("getCompModuleForFileUri (" + uri + ")");
        if (uri.equals(cachedCompModuleForFileUri_Uri)) {
            return getResult(cachedCompModuleForFileUri);
        }

        try {
            String path = fileUriToPath(uri);

            // Try to return a nullModule object for non-AlloyMarkdown files.
            // Not a big deal if the file has not been cached
            String contents = fileContents.get(uri);
            if (contents != null && !isAlloyFile(path, contents)) {
                return CompUtil.nullModule();
            }

            cachedCompModuleForFileUri = Either.forLeft(CompUtil.parseEverything_fromFile(null, fileContentsPathBased(), path, 2));

        } catch (Err err) {
            log("getCompModuleForFileUri(): error in parsing: " + err.toString());
            fileUrisOfLastPublishedDiagnostics.add(uri);

            client.publishDiagnostics(toPublishDiagnosticsParams(err));

            if (err instanceof ErrorSyntax)
                latestFileUrisWithSyntaxError.add(uri);

            cachedCompModuleForFileUri = Either.forRight(err);
            throw err;
        }

        if (latestFileUrisWithSyntaxError.contains(uri)) {
            client.publishDiagnostics(newPublishDiagnosticsParams(uri, Arrays.asList()));
            latestFileUrisWithSyntaxError.remove(uri);
        }
        cachedCompModuleForFileUri_Uri = uri;
        return getResult(cachedCompModuleForFileUri);
    }

    @Override
    public CompletableFuture<Hover> hover(TextDocumentPositionParams position) {
        //log("hover request");
        String hoverStr = null;
        try {

            String uri = position.getTextDocument().getUri();
            String text = fileContents.get(uri);
            CompModule module = getCompModuleForFileUri(uri);

            Pos pos = positionToPos(position.getPosition());
            Expr expr = module.find(pos);
            if (expr instanceof ExprBad) {
                hoverStr = expr.toString();
            } else if (expr != null) {
                Clause referenced = expr.referenced();
                if (referenced != null) {
                    hoverStr = referenced.explain();
                } else if (expr instanceof ExprConstant) {
                    String token = pos.substring(text);
                    if (token != null) {
                        String match = expr.toString();
                        if (!Objects.equals(token, match))
                            hoverStr = match;
                    }
                }
            }
        } catch (Exception e) {
            // ignore compile errors etc.
        }
        if (hoverStr != null) {
            MarkupContent markupContent = new MarkupContent();
            markupContent.setKind("markdown");

            hoverStr = "```\n" + hoverStr + "\n```";

            markupContent.setValue(hoverStr);
            Hover res = new Hover();
            res.setContents(markupContent);
            return CompletableFuture.completedFuture(res);
        } else {
            return CompletableFuture.completedFuture(null);
        }
    }

    @Override
    public CompletableFuture<SignatureHelp> signatureHelp(TextDocumentPositionParams position) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<List< ? extends Location>> definition(TextDocumentPositionParams position) {
        try {
            String uri = position.getTextDocument().getUri();
            String text = fileContents.get(uri);
            String path = fileUriToPath(uri);

            CompModule module = getCompModuleForFileUri(uri);
            Pos pos = positionToPos(position.getPosition(), path);
            pos = getCurrentWordSelectionAsPos(text, pos);
            Expr expr = module.find(pos);

            log("definition request for: " + expr);

            if (expr != null) {
                Clause clause = expr.referenced();
                if (clause != null) {
                    Pos where = clause.pos();

                    //if path includes the jar, replace it by the created temp dir containing alloy models
                    String fileName = filePathResolved(where.filename);

                    String targetUri = where.sameFile(module.pos()) ? uri : filePathToUri(fileName);
                    Location res = Lsp4jUtil.newLocation(createRangeFromPos(where), targetUri);
                    return CompletableFuture.completedFuture(Arrays.asList(res));
                }
            }

        } catch (Exception ex) {
            System.err.println("Error in providing definition: " + ex.toString());
        }
        return CompletableFuture.completedFuture(Arrays.asList());
    }



    @Override
    public CompletableFuture<List< ? extends Location>> references(ReferenceParams params) {

        String uri = params.getTextDocument().getUri();
        String text = fileContents.get(uri);
        String path = fileUriToPath(uri);

        try {
            CompModule module = getCompModuleForFileUri(params.getTextDocument().getUri());

            Pos pos = getPosOfSymbolFromPositionInOpenDoc(params.getTextDocument().getUri(), params.getPosition());
            pos = getCurrentWordSelectionAsPos(text, pos).withFilename(path);

            String dir = this.directory != null ? this.directory : new File(path).getParent();
            List<Location> res = findAllReferencesGlobally(module, pos, dir, true, true).stream().map(ref -> posToLocation(ref)).collect(Collectors.toList());
            return CompletableFuture.completedFuture(res);
        } catch (Err err) {
            client.showMessage(newMessageParams("There are errors. Fix them first.", MessageType.Warning));
            return CompletableFuture.completedFuture(null);
        }
    }

    @Override
    public CompletableFuture<WorkspaceEdit> rename(RenameParams params) {
        String uri = params.getTextDocument().getUri();
        String text = fileContents.get(uri);
        String path = fileUriToPath(uri);

        try {
            CompModule module = getCompModuleForFileUri(uri);

            Pos pos = getPosOfSymbolFromPositionInOpenDoc(uri, params.getPosition());
            pos = getCurrentWordSelectionAsPos(text, pos).withFilename(path);

            Expr expr = module.find(pos);
            Pos targetPos = expr.referenced() != null ? expr.referenced().pos() : expr.pos;

            CompModule targetModule = CompUtil.parseEverything_fromFile(null, fileContentsPathBased(), filePathResolved(targetPos.filename));

            Expr targetExpr = targetModule.find(targetPos);

            Map<String,List<TextEdit>> changes = new HashMap<>();

            String dir = this.directory != null ? this.directory : new File(path).getParent();
            List<Pos> refs = findAllReferencesGlobally(module, pos, dir, false, false);

            if (targetExpr instanceof Sig) {
                targetPos = ((Sig) targetExpr).labelPos;
            } else if (targetExpr instanceof Field) {
                targetPos = ((Field) targetExpr).labelPos;
            } else if (targetExpr instanceof Func) {
                targetPos = ((Func) targetExpr).labelPos;
            } else if (targetExpr instanceof Assert) {
                targetPos = ((Assert) targetExpr).labelPos;
            } else if (targetExpr instanceof Macro) {
                targetPos = ((Macro) targetExpr).namePos;
            }

            WorkspaceEdit wEdit = new WorkspaceEdit();
            Stream.concat(refs.stream().distinct(), Stream.of(targetPos)).forEach(refPos -> {
                TextEdit edit = new TextEdit();

                edit.setRange(createRangeFromPos(refPos));
                edit.setNewText(params.getNewName());

                String refUri = filePathToUri(filePathResolved(refPos.filename));

                if (!changes.containsKey(refUri))
                    changes.put(refUri, new ArrayList<>());
                changes.get(refUri).add(edit);
            });

            wEdit.setChanges(changes);

            return CompletableFuture.completedFuture(wEdit);

        } catch (Err err) {
            client.showMessage(newMessageParams("Cannot rename symbol while there are errors. Fix the errors first.", MessageType.Warning));
            return CompletableFuture.completedFuture(null);
        }
    }

    Pos getPosOfSymbolFromPositionInOpenDoc(String uri, Position position) {
        String path = fileUriToPath(uri);
        String text = fileContents.get(uri);

        Pos pos = positionToPos(position, path);
        pos = getCurrentWordSelectionAsPos(text, pos);
        return pos;
    }

    @Override
    public CompletableFuture<List< ? extends DocumentHighlight>> documentHighlight(TextDocumentPositionParams position) {

        try {
            CompModule module = getCompModuleForFileUri(position.getTextDocument().getUri());

            Pos pos = getPosOfSymbolFromPositionInOpenDoc(position.getTextDocument().getUri(), position.getPosition());
            List<Expr> refs = findAllReferences(module, pos, true);

            String path = fileUriToPath(position.getTextDocument().getUri());
            List<DocumentHighlight> res = refs.stream().filter(ref -> path.equals(ref.pos.filename)).map(ref -> {
                DocumentHighlight highlight = new DocumentHighlight();

                highlight.setKind(DocumentHighlightKind.Text);
                highlight.setRange(createRangeFromPos(ref.pos));
                return highlight;
            }).collect(Collectors.toList());

            return CompletableFuture.completedFuture(res);

        } catch (Exception ex) {
            return CompletableFuture.completedFuture(null);
        }
    }

    @Override
    public CompletableFuture<List< ? extends SymbolInformation>> documentSymbol(DocumentSymbolParams params) {
        try {
            CompModule module = getCompModuleForFileUri(params.getTextDocument().getUri());
            return CompletableFuture.completedFuture(moduleSymbols(module));
        } catch (Exception ex) {
            return CompletableFuture.completedFuture(null);
        }
    }

    private List<SymbolInformation> folderSymbols(String dir) {
        List<SymbolInformation> res = new ArrayList<>();

        for (File child : alloyFilesInDir(dir)) {
            String filePath = fileUriToPath(child.toURI().toString());
            try {
                CompModule module = CompUtil.parseEverything_fromFile(null, fileContentsPathBased(), filePath);
                res.addAll(moduleSymbols(module));
            } catch (Exception ex) {
                log("error parsing " + child);
            }
        }

        return res;
    }

    private static List<SymbolInformation> moduleSymbols(CompModule module) {
        Stream<SymbolInformation> commands = module.getAllCommands().stream().map(c -> newSymbolInformation(c.label, posToLocation(c.pos), SymbolKind.Event));

        Stream<SymbolInformation> sigs = module.getAllSigs().makeConstList().stream().map(sig -> newSymbolInformation(sig.label, posToLocation(sig.pos), sig.isEnum != null ? SymbolKind.Enum : sig.isEnumMember() ? SymbolKind.EnumMember : sig.isOne != null || sig.isLone != null ? SymbolKind.Object : SymbolKind.Class));

        Stream<SymbolInformation> fields = module.getAllSigs().makeConstList().stream().flatMap(sig -> sig.getFields().makeConstList().stream()).map(field -> {
            SymbolInformation symbolInfo = newSymbolInformation(field.label, posToLocation(field.pos), SymbolKind.Field);
            symbolInfo.setContainerName(removeThisPrefix(field.sig.label));
            return symbolInfo;
        });

        Stream<SymbolInformation> funcs = module.getAllFunc().makeConstList().stream().map(func -> newSymbolInformation(func.label, posToLocation(func.pos), func.isPred ? SymbolKind.Boolean : SymbolKind.Function));

        Stream<SymbolInformation> macros = module.getAllMacros().makeConstList().stream().map(macro -> newSymbolInformation(macro.name, posToLocation(macro.pos), SymbolKind.Constructor));

        Stream<SymbolInformation> assertions = module.getAllAssertions().stream().map(assertion -> newSymbolInformation(assertion.label, posToLocation(assertion.pos), SymbolKind.Property));

        return Stream.of(commands, sigs, fields, funcs, assertions, macros).flatMap(x -> x).map(x -> {
            x.setName(removeThisPrefix(x.getName()));
            return x;
        })
                     //.sorted((sym1,sym2) -> positionCompare(sym1.getLocation().getRange().getStart(), sym2.getLocation().getRange().getStart()))
                     .collect(Collectors.toList());
    }

    @Override
    public CompletableFuture<List< ? extends Command>> codeAction(CodeActionParams params) {
        return CompletableFuture.completedFuture(null);
    }

    List<Pair<edu.mit.csail.sdg.ast.Command,Command>> getCommands(String uri) {
        CompModule module;

        try {
            module = getCompModuleForFileUri(uri);
        } catch (Exception e) {
            return Arrays.asList();
        }

        ConstList<edu.mit.csail.sdg.ast.Command> commands = module.getAllCommands();

        ArrayList<Pair<edu.mit.csail.sdg.ast.Command,Command>> res = new ArrayList<>();

        for (int i = 0; i < commands.size(); i++) {
            edu.mit.csail.sdg.ast.Command command = commands.get(i);
            Position position = posToPosition(command.pos);
            CodeLens codeLens = new CodeLens();
            codeLens.setRange(createRange(position, position));
            Command vsCommand = new Command("Execute", "ExecuteAlloyCommand");
            vsCommand.setArguments(Arrays.asList(uri, i, position.getLine(), position.getCharacter()));
            codeLens.setCommand(vsCommand);

            res.add(new Pair<>(command, vsCommand));
        }

        if (latestFileUrisWithSyntaxError.contains(uri)) {
            client.publishDiagnostics(newPublishDiagnosticsParams(uri, Arrays.asList()));
            latestFileUrisWithSyntaxError.remove(uri);
        }
        return res;
    }

    @Override
    public CompletableFuture<List< ? extends CodeLens>> codeLens(CodeLensParams params) {

        List<CodeLens> res = getCommands(params.getTextDocument().getUri()).stream().map(pair -> {
            edu.mit.csail.sdg.ast.Command command = pair.a;
            Command vsCommand = pair.b;

            CodeLens codeLens = new CodeLens();
            codeLens.setRange(createRangeFromPos(command.pos));
            codeLens.setCommand(vsCommand);

            return codeLens;
        }).collect(Collectors.toList());

        return CompletableFuture.completedFuture(res);
    }

    @Override
    public CompletableFuture<List<DocumentLink>> documentLink(DocumentLinkParams params) {

        List<DocumentLink> links = getCommands(params.getTextDocument().getUri()).stream().map(pair -> {
            edu.mit.csail.sdg.ast.Command command = pair.a;
            Command vsCommand = pair.b;

            DocumentLink link = new DocumentLink();
            link.setRange(createRangeFromPos(command.commandKeyword.pos));
            List<Object> args = vsCommand.getArguments();
            Gson gson = new Gson();
            try {
                java.net.URI path = new java.net.URI((String) args.get(0));
                args.set(0, path.toString());
                System.err.println("gson.toJson(args): " + gson.toJson(args));
                link.setTarget("command:" + vsCommand.getCommand() + "?" + gson.toJson(args));
                // URLEncoder.encode(gson.toJson(args), "UTF-8") );
                // } catch (UnsupportedEncodingException e1) {
            } catch (URISyntaxException e) {
            }

            return link;
        }).collect(Collectors.toList());

        return CompletableFuture.completedFuture(links);

    }

    @JsonRequest
    public CompletableFuture<Void> ListAlloyCommands(JsonPrimitive documentUri) {
        log("ListAlloyCommands called with " + documentUri + ", of type " + documentUri.getClass().getName());
        List<CommandsListResultItem> res = getCommands(documentUri.getAsString()).stream().map(pair -> new CommandsListResultItem(pair.a.toString(), pair.b)).collect(Collectors.toList());

        client.commandsListResult(new CommandsListResult(res));
        return CompletableFuture.completedFuture(null);
    }

    private final HashSet<String> fileUrisOfLastPublishedDiagnostics = new HashSet<>();
    private final Set<String>     latestFileUrisWithSyntaxError      = new HashSet<>();

    @JsonRequest
    public CompletableFuture<Void> ExecuteAlloyCommand(com.google.gson.JsonArray params) {
        log("ExecuteAlloyCommand() called with " + params + ", " + params.getClass());
        String uri = params.get(0).getAsString();
        int ind = params.get(1).getAsInt();
        int line = params.get(2).getAsInt(), character = params.get(3).getAsInt();

        Position position = new Position(line, character);
        Pos pos = positionToPos(position);
        String fileString = fileContents.get(uri);
        // Ugly hack to make the uri look like what it was if invoked through links
        // if (fileString == null) {
        // 	java.net.URI uriObj = new java.net.URI(uri);
        // 	String newPath =  uriObj.getRawPath().replace(":", "%3A");
        // 	String newUri = uriObj.getScheme() + newPath;
        // 	fileString = fileContents.get(newUri);
        // }
        // Another ugly hack to make things work if invoked through links (which makes the uri look different)
        if (fileString == null) {
            String uriPath = fileUriToPath(uri);
            for (Map.Entry<String,String> entry : fileContents.entrySet()) {
                if (fileUriToPath(entry.getKey()).equals(uriPath)) {
                    fileString = entry.getValue();
                    uri = entry.getKey();
                    break;
                }
            }
        }
        if (fileString == null) {
            System.err.println("Error in ExecuteAlloyCommand: failed to retrieve file contents for " + uri);
            return CompletableFuture.completedFuture(null);
        }
        CompModule module = CompUtil.parseOneModule(fileString);
        ConstList<edu.mit.csail.sdg.ast.Command> commands = module.getAllCommands();
        edu.mit.csail.sdg.ast.Command command = commands.stream().filter(comm -> comm.pos().y == pos.y && comm.pos.x == pos.x).findFirst().orElse(null);
        if (command != null || ind == -1) {
            String uriToShutUpStupidJava = uri;
            CompletableFuture.runAsync(() -> doRun(uriToShutUpStupidJava, ind));
        } else {
            System.err.println("no matching command found");
        }

        return CompletableFuture.completedFuture(null);
    }

    @JsonRequest
    public CompletableFuture<Void> StopExecution(Object o) {
        log("Stop req received");
        doStop(2);

        AlloyLSMessage alloyMsg = new AlloyLSMessage(RunCompleted, "Stopped");
        alloyMsg.bold = true;
        client.showExecutionOutput(alloyMsg);

        return CompletableFuture.completedFuture(null);
    }

    @JsonRequest
    public CompletableFuture<Void> OpenModel(com.google.gson.JsonPrimitive link) {
        log("OpenModel() called with " + link.getAsString());
        log(" , of type" + link.getClass().getName());
        doVisualize(link.getAsString());
        return CompletableFuture.completedFuture(null);
    }



    @Override
    public CompletableFuture<CodeLens> resolveCodeLens(CodeLens unresolved) {
        return CompletableFuture.completedFuture(unresolved);
    }

    @Override
    public CompletableFuture<List< ? extends TextEdit>> formatting(DocumentFormattingParams params) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<List< ? extends TextEdit>> rangeFormatting(DocumentRangeFormattingParams params) {
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<List< ? extends TextEdit>> onTypeFormatting(DocumentOnTypeFormattingParams params) {
        return CompletableFuture.completedFuture(null);
    }


    private Map<String,String> fileContentsPathBased() {
        HashMap<String,String> res = new HashMap<String,String>();
        fileContents.entrySet().stream().forEach(entry -> res.put(fileUriToPath(entry.getKey()), entry.getValue()));
        return res;
    }

    private HashMap<String,String> fileContents = new HashMap<>();

    @Override
    public void didOpen(DidOpenTextDocumentParams params) {
        String text = params.getTextDocument().getText();
        String uri = params.getTextDocument().getUri();
        fileContents.put(uri, text);
    }

    @Override
    public void didChange(DidChangeTextDocumentParams params) {
        // https://raw.githubusercontent.com/eclipse/eclipse.jdt.ls/0ed1bf259b3edb4f184804a9df14c95ef468d4e9/org.eclipse.jdt.ls.core/src/org/eclipse/jdt/ls/core/internal/handlers/DocumentLifeCycleHandler.java
        String text = params.getContentChanges().get(0).getText();
        String uri = params.getTextDocument().getUri();
        fileContents.put(uri, text);

        cachedCompModuleForFileUri = null;
        cachedCompModuleForFileUri_Uri = null;
    }

    @Override
    public void didSave(DidSaveTextDocumentParams params) {
        String text = params.getText();

        if (text != null) {
            String uri = params.getTextDocument().getUri();
            fileContents.put(uri, text);

            cachedCompModuleForFileUri = null;
            cachedCompModuleForFileUri_Uri = null;
        }
    }

    // WorkspaceService methods
    @Override
    public void didClose(DidCloseTextDocumentParams params) {
        fileContents.remove(params.getTextDocument().getUri());
    }

    @Override
    public CompletableFuture<List< ? extends SymbolInformation>> symbol(WorkspaceSymbolParams params) {

        if (this.directory == null)
            return CompletableFuture.completedFuture(null);

        List<SymbolInformation> res = folderSymbols(this.directory).stream().filter(symbol -> {
            return symbol.getName().toLowerCase().contains(params.getQuery().toLowerCase());
        }).collect(Collectors.toList());

        return CompletableFuture.completedFuture(res);
    }

    @Override
    public void didChangeConfiguration(DidChangeConfigurationParams params) {
    }

    @Override
    public void didChangeWatchedFiles(DidChangeWatchedFilesParams params) {
    }

    static String removeThisPrefix(String name) {
        if (name.startsWith("this/")) {
            return name.substring("this/".length());
        }
        return name;
    }

    private PublishDiagnosticsParams toPublishDiagnosticsParams(Err err) {
        return toPublishDiagnosticsParamsList(Arrays.asList(err)).get(0);
    }

    private List<PublishDiagnosticsParams> toPublishDiagnosticsParamsList(List<Err> errors) {

        Map<String,List<Err>> map = errors.stream().collect(Collectors.groupingBy(warning -> warning.pos.filename));
        return map.entrySet().stream().map(entry -> {

            List<Diagnostic> diags = entry.getValue().stream().map(err -> {
                Diagnostic diag = newDiagnostic(err.msg, createRangeFromPos(err.pos));
                diag.setSeverity(err instanceof ErrorWarning ? DiagnosticSeverity.Warning : DiagnosticSeverity.Error);

                return diag;
            }).collect(Collectors.toList());

            return newPublishDiagnosticsParams(filePathToUri(entry.getKey()), diags);
        }).collect(Collectors.toList());
    }

    private String newInstance;
    private VizGUI viz;

    // edu.mit.csail.sdg.alloy4whole.SimpleGUI.doRun(Integer)
    private void doRun(String fileURI, Integer commandIndex) {
        CompModule module = CompUtil.parseOneModule(fileContents.get(fileURI));
        ConstList<edu.mit.csail.sdg.ast.Command> commands = module.getAllCommands();

        final int index = commandIndex;
        if (WorkerEngine.isBusy() || (commands == null))
            return;
        if (commands.size() == 0 && index != -2 && index != -3) {
            // log.logRed("There are no commands to execute.\n\n");
            return;
        }
        int i = index;
        if (i >= commands.size())
            i = commands.size() - 1;
        // SimpleCallback1 cb = new SimpleCallback1(this, null, log,
        // VerbosityPref.get().ordinal(), latestAlloyVersionName, latestAlloyVersion);
        SimpleTask1 task = new SimpleTask1();
        A4Options opt = new A4Options();
        opt.tempDirectory = SimpleGUI.alloyHome(null) + fs + "tmp";
        opt.solverDirectory = SimpleGUI.alloyHome(null) + fs + "binary";
        opt.recordKodkod = RecordKodkod.get();
        opt.noOverflow = NoOverflow.get();
        opt.unrolls = Version.experimental ? Unrolls.get() : (-1);
        opt.skolemDepth = SkolemDepth.get();
        opt.coreMinimization = CoreMinimization.get();
        opt.inferPartialInstance = InferPartialInstance.get();
        opt.coreGranularity = CoreGranularity.get();

        log("cwd :" + Paths.get("").toAbsolutePath());

        String fileNameDecoded;
        try {
            fileNameDecoded = URIUtil.toFile(new URI(fileURI)).getPath();

        } catch (Exception ex) {
            System.err.println("failed to parse uri");
            return;
        }
        log("fileNameDecoded:" + fileNameDecoded);

        opt.originalFilename = fileNameDecoded;// new File(decodeUrl(uri)).getPath();// Util.canon(decodeUrl(uri));
        opt.solver = Solver.get();
        task.bundleIndex = i;
        task.bundleWarningNonFatal = WarningNonfatal.get();
        // task.map = text.takeSnapshot();
        task.options = opt.dup();
        task.resolutionMode = (Version.experimental && ImplicitThis.get()) ? 2 : 1;
        task.tempdir = SimpleGUI.maketemp(null);

        try {
            int newmem = SubMemory.get(), newstack = SubStack.get();
            if (newmem != subMemoryNow || newstack != subStackNow)
                WorkerEngine.stop();

            WorkerCallback cb = getWorkerCallback();

            log("actually running the task");
            // if (AlloyCore.isDebug() && VerbosityPref.get() == Verbosity.FULLDEBUG)
            //WorkerEngine.runLocally(task, cb);
            // else
            WorkerEngine.run(task, newmem, newstack, SimpleGUI.alloyHome(null) + fs + "binary", "", cb);
            subMemoryNow = newmem;
            subStackNow = newstack;
        } catch (Throwable ex) {
            WorkerEngine.stop();
            System.err.println("Fatal Error: Solver failed due to unknown reason. exception: \n" + ex.toString());
            // log.logBold("Fatal Error: Solver failed due to unknown reason.\n" + "One
            // possible cause is that, in the Options menu, your specified\n" + "memory size
            // is larger than the amount allowed by your OS.\n" + "Also, please make sure
            // \"java\" is in your program path.\n");
            // log.logDivider();
            // log.flush();
            doStop(2);
        }
        return;
    }

    private WorkerCallback getVizWorkerCallback() {
        return new WorkerCallback() {

            @Override
            public void fail() {
                AlloyLSMessage alloyMsg = new AlloyLSMessage(AlloyLSMessageType.RunCompleted, "failure");
                client.showExecutionOutput(alloyMsg);

            }

            @Override
            public void done() {
                viz.loadXML(newInstance, true);

            }

            @Override
            public void callback(Object msg) {
                Either<List<AlloyLSMessage>,Err> alloyMsgOrWarning = solverCallbackMsgToAlloyMsg(msg);

                if (alloyMsgOrWarning.isLeft()) {
                    for (AlloyLSMessage alloyMsg : alloyMsgOrWarning.getLeft()) {
                        if (alloyMsg.message != null && !alloyMsg.message.isEmpty())
                            //client.showExecutionOutput(alloyMsg);
                            client.logMessage(newMessageParams(alloyMsg.message, MessageType.Log));
                    }

                } else {
                    //warnings.add(alloyMsgOrWarning.getRight());
                }

            }
        };
    }

    private WorkerCallback getWorkerCallback() {
        return new WorkerCallback() {

            List<Err> warnings = new ArrayList<>();

            @Override
            public void callback(Object msg) {

                // MessageParams messageParams= new MessageParams();
                // messageParams.setMessage(solverCallbackMsgToString(msg));
                // client.showMessage(messageParams);
                //					if(messageParams.getMessage() != null && !messageParams.getMessage().isEmpty())
                //						client.showAlloyOutput(messageParams);

                Either<List<AlloyLSMessage>,Err> alloyMsgOrWarning = solverCallbackMsgToAlloyMsg(msg);

                if (alloyMsgOrWarning.isLeft()) {
                    for (AlloyLSMessage alloyMsg : alloyMsgOrWarning.getLeft()) {
                        if (alloyMsg.message != null && !alloyMsg.message.isEmpty())
                            client.showExecutionOutput(alloyMsg);
                    }

                } else {
                    Err err = alloyMsgOrWarning.getRight();

                    if (Pos.UNKNOWN.equals(err.pos) || err.pos == null) {
                        AlloyLSMessage errMsg = new AlloyLSMessage(AlloyLSMessageType.Warning, err.msg + "\n");
                        errMsg.bold = true;
                        client.showExecutionOutput(errMsg);
                    }
                    warnings.add(alloyMsgOrWarning.getRight());
                }
            }

            @Override
            public void done() {
                // MessageParams messageParams= new MessageParams();
                // messageParams.setMessage("done");
                // client.showMessage(messageParams);
                // client.showAlloyOutput(messageParams);
                if (warnings.size() > 0)
                    client.showExecutionOutput(new AlloyLSMessage(AlloyLSMessageType.RunResult, "There were errors/warnings!"));

                client.showExecutionOutput(new AlloyLSMessage(AlloyLSMessageType.RunCompleted, ""));

                publishDiagnostics();
            }

            @Override
            public void fail() {
                AlloyLSMessage alloyMsg = new AlloyLSMessage(AlloyLSMessageType.RunCompleted, "failure");
                client.showExecutionOutput(alloyMsg);
                publishDiagnostics();
            }

            void publishDiagnostics() {

                //cleaning previously reported diagnostics
                if (fileUrisOfLastPublishedDiagnostics != null)
                    fileUrisOfLastPublishedDiagnostics.stream().forEach(item -> {
                        PublishDiagnosticsParams diagnostics = new PublishDiagnosticsParams();
                        diagnostics.setUri(item);
                        client.publishDiagnostics(diagnostics);
                    });

                List<PublishDiagnosticsParams> diagnosticsParamsList = toPublishDiagnosticsParamsList(warnings);

                diagnosticsParamsList.forEach(diagsParams -> client.publishDiagnostics(diagsParams));

                fileUrisOfLastPublishedDiagnostics.clear();
                fileUrisOfLastPublishedDiagnostics.addAll(diagnosticsParamsList.stream().map(item -> item.getUri()).collect(Collectors.toList()));

            }

        };
    }

    // edu.mit.csail.sdg.alloy4whole.SimpleReporter.SimpleCallback1.callback(Object)
    public Either<List<AlloyLSMessage>,Err> solverCallbackMsgToAlloyMsg(Object msg) {
        StringBuilder span = new StringBuilder();
        AlloyLSMessage alloyMsg = new AlloyLSMessage(AlloyLSMessageType.RunInProgress, null);

        List<AlloyLSMessage> resMsgs = new ArrayList<>();
        resMsgs.add(alloyMsg);

        final int verbosity = 0;
        if (msg == null) {
            span.append("Done\n");
        } else if (msg instanceof String) {
            span.append(((String) msg).trim() + "\n");
        } else if (msg instanceof Throwable) {
            for (Throwable ex = (Throwable) msg; ex != null; ex = ex.getCause()) {
                if (ex instanceof OutOfMemoryError) {
                    span.append("\nFatal Error: the solver ran out of memory!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase memory under the Options menu.\n");
                }
                if (ex instanceof StackOverflowError) {
                    span.append("\nFatal Error: the solver ran out of stack space!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase stack under the Options menu.\n");
                }
            }
            if (msg instanceof Err) {
                log("Err msg from solver: " + msg.toString());
                Err ex = (Err) msg;
                String text = "fatal";
                boolean fatal = false;
                if (ex instanceof ErrorSyntax)
                    text = "syntax";
                else if (ex instanceof ErrorType)
                    text = "type";
                else
                    fatal = true;
                if (ex.pos == Pos.UNKNOWN)
                    span.append("A " + text + " error has occurred:  ");
                else
                    span.append("A " + text + " error has occurred:  " + "POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
                // if (verbosity > 2) {
                // 	span.log("(see the ");
                // 	span.logLink("stacktrace", "MSG: " + ex.dump());
                // 	span.log(")\n");
                // } else {
                // 	span.log("\n");
                // }
                span.append(ex.msg.trim()); // logIndented
                return Either.forRight(ex);
                //span.append("\n");
                // if (fatal && latestVersion > Version.buildNumber())
                // 	span.logBold("\nNote: You are running Alloy build#" + Version.buildNumber() + ",\nbut the most recent is Alloy build#" + latestVersion + ":\n( version " + latestName + " )\nPlease try to upgrade to the newest version," + "\nas the problem may have been fixed already.\n");

                // if (!fatal)
                // 	gui.doVisualize("POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
            } else /* if (msg instanceof Throwable) */ {
                log("exception msg from solver: " + msg.toString());
                Throwable ex = (Throwable) msg;
                span.append(ex.toString().trim() + "\n");
                // span.flush();
            }
        } else if ((msg instanceof Object[])) {
            Object[] array = (Object[]) msg;
            if (array[0].equals("pop")) {
                // span.setLength(len2);
                String x = (String) (array[1]);
                span.append(x);
                alloyMsg.replaceLast = true;
                // if (viz != null && x.length() > 0)
                // 	OurDialog.alert(x);
            }
            if (array[0].equals("declare")) {
                //gui.doSetLatest((String) (array[1]));
                newInstance = (String) (array[1]);
                // ==========
            }
            if (array[0].equals("S2")) {
                // len3 = len2 = span.getLength();
                span.append("" + array[1]);
            }
            if (array[0].equals("R3")) {
                //span.setLength(len3);
                span.append("" + array[1]);
            }
            if (array[0].equals("link")) {
                log("link message!!!");
                //span.logLink((String) (array[1]), (String) (array[2]));
                span.append(array[1].toString());
                alloyMsg.link = (String) array[2];
                alloyMsg.messageType = AlloyLSMessageType.RunResult;

            }
            if (array[0].equals("bold")) {
                span.append("" + array[1]);
                alloyMsg.bold = true;
                //alloyMsg.replaceLast = true;
            }
            if (array[0].equals("")) {
                span.append("" + array[1]);
            }
            if (array[0].equals("scope") && verbosity > 0) {
                span.append("   " + array[1]);
            }
            if (array[0].equals("bound") && verbosity > 1) {
                span.append("   " + array[1]);
            }
            if (array[0].equals("resultCNF")) {
                // results.add(null);
                // span.setLength(len3);
                // span.log(" File written to " + array[1] + "\n\n");
            }
            if (array[0].equals("debug") && verbosity > 2) {
                span.append("   " + array[1] + "\n");
                // len2 = len3 = span.getLength();
            }
            if (array[0].equals("translate")) {
                span.append("   " + array[1]);
                // len3 = span.getLength();
                span.append("   Generating CNF...\n");
            }
            if (array[0].equals("solve")) {
                // span.setLength(len3);
                span.append("   " + array[1]);
                // len3 = span.getLength();
                span.append("   Solving...\n");
            }
            if (array[0].equals("warnings")) {
                // if (warnings.size() == 0)
                // 	span.setLength(len2);
                // else if (warnings.size() > 1)
                // 	span.logBold("Note: There were " + warnings.size() + " compilation warnings. Please scroll up to see them.\n\n");
                // else
                // 		span.append("Note: There was 1 compilation wrearning. Please scroll up to see
                // 		them.\n\n");
                // 		span.append("There were warnings!");
                // if (warnings.size() > 0 && Boolean.FALSE.equals(array[1])) {
                // 	Pos e = warnings.iterator().next().pos;
                // 	gui.doVisualize("POS: " + e.x + " " + e.y + " " + e.x2 + " " + e.y2 + " " + e.filename);
                // 	span.logBold("Warnings often indicate errors in the model.\n" + "Some warnings can affect the soundness of the analysis.\n" + "To proceed despite the warnings, go to the Options menu.\n");
                // }
            }
            if (array[0].equals("warning")) {
                ErrorWarning e = (ErrorWarning) (array[1]);
                // if (!warnings.add(e))
                // 	return;
                Pos p = e.pos;
                // span.logLink("Warning #" + warnings.size(), "POS: " + p.x + " " + p.y + " " + p.x2 + " " + p.y2 + " " + p.filename);
                span.append("Warning " + e.msg.trim());// #" + warnings.size(), "POS: " + p.x + " " + p.y + " " + p.x2 +
                                                       // " " + p.y2 + " " + p.filename);
                return Either.forRight(e);
                // span.log("\n");
                // span.logIndented(e.msg.trim());
                // span.log("\n\n");
            }
            if (array[0].equals("sat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String filename = (String) (array[3]), formula = (String) (array[4]);
                // results.add(filename);
                (new File(filename)).deleteOnExit();
                // gui.doSetLatest(filename);
                // span.setLength(len3);
                span.append("   ");
                // span.logLink(chk ? "Counterexample" : "Instance", "XML: " + filename);
                span.append(chk ? "Counterexample" : "Instance");// , "XML: " + filename);
                alloyMsg.link = "XML: " + filename;
                alloyMsg.messageType = AlloyLSMessageType.RunResult;
                alloyMsg.replaceLast = true;
                alloyMsg.bold = true;
                span.append(" found. ");
                // span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.append(chk ? "Assertion" : "Predicate");// , formula);
                span.append(chk ? " is invalid" : " is consistent");
                if (expects == 0)
                    span.append(", contrary to expectation");
                else if (expects == 1)
                    span.append(", as expected");
                span.append(". ");
                //span.append(". " + array[5] + "ms.\n\n");
                alloyMsg.lineBreak = false;
                resMsgs.add(new AlloyLSMessage(AlloyLSMessageType.RunResult, array[5] + "ms.\n\n"));
            }
            if (array[0].equals("metamodel")) {
                // String outf = (String) (array[1]);
                // span.setLength(len2);
                // (new File(outf)).deleteOnExit();
                // gui.doSetLatest(outf);
                // span.logLink("Metamodel", "XML: " + outf);
                // span.log(" successfully generated.\n\n");
            }
            if (array[0].equals("minimizing")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                // int expects = (Integer) (array[2]);
                // span.setLength(len3);
                // span.log(chk ? "   No counterexample found." : "   No instance found.");
                span.append(chk ? "   No counterexample found. " : "   No instance found. ");
                if (chk)
                    span.append(" Assertion may be valid");
                else
                    span.append(" Predicate may be inconsistent");
                // if (expects == 1)
                // 	span.log(", contrary to expectation");
                // else if (expects == 0)
                // 	span.log(", as expected");
                span.append(". " + array[4] + "ms.\n");
                // span.logBold("   Minimizing the unsat core of " + array[3] + " entries...\n");
            }
            if (array[0].equals("unsat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String formula = (String) (array[4]);
                // span.setLength(len3);
                alloyMsg.messageType = AlloyLSMessageType.RunResult;
                alloyMsg.replaceLast = true;
                alloyMsg.bold = true;
                span.append(chk ? "   No counterexample found. " : "   No instance found. ");
                span.append(chk ? "Assertion" : "Predicate");// , formula);
                span.append(chk ? " may be valid" : " may be inconsistent");
                if (expects == 1)
                    span.append(", contrary to expectation");
                else if (expects == 0)
                    span.append(", as expected");
                if (array.length == 5) {
                    span.append(". ");
                    alloyMsg.lineBreak = false;
                    resMsgs.add(new AlloyLSMessage(RunResult, array[3] + "ms.\n\n"));
                    // span.flush();
                } else {
                    String core = (String) (array[5]);
                    int mbefore = (Integer) (array[6]), mafter = (Integer) (array[7]);
                    span.append(". " + array[3] + "ms.\n");
                    if (core.length() == 0) {
                        // results.add("");
                        span.append("   No unsat core is available in this case. ");

                        resMsgs.add(new AlloyLSMessage(RunResult, array[8] + "ms.\n\n"));
                        // span.flush();
                    } else {

                        // results.add(core);
                        (new File(core)).deleteOnExit();
                        span.append("   ");
                        //span.append("Core");// , core);

                        AlloyLSMessage coreLinkMsg = new AlloyLSMessage(RunResult, "core");
                        coreLinkMsg.link = core;
                        resMsgs.add(coreLinkMsg);

                        AlloyLSMessage nextMsg = new AlloyLSMessage(RunResult, null);
                        if (mbefore <= mafter)
                            nextMsg.message = (" contains " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
                        else
                            nextMsg.message = (" reduced from " + mbefore + " to " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
                        resMsgs.add(nextMsg);
                    }
                }
            }
        }
        alloyMsg.message = span.toString();
        return Either.forLeft(resMsgs);
    }

    /**
     * This method stops the current run or check (how==0 means DONE, how==1 means
     * FAIL, how==2 means STOP).
     */
    void doStop(Integer how) {
        int h = how;
        if (h != 0) {
            if (h == 2 && WorkerEngine.isBusy()) {
                WorkerEngine.stop();
                //log.logBold("\nSolving Stopped.\n");
                //log.logDivider();
            }
            WorkerEngine.stop();
        }
        // runmenu.setEnabled(true);
        // runbutton.setVisible(true);
        // showbutton.setEnabled(true);
        // stopbutton.setVisible(false);
        // if (latestAutoInstance.length() > 0) {
        // 	String f = latestAutoInstance;
        // 	latestAutoInstance = "";
        // 	if (subrunningTask == 2)
        // 		viz.loadXML(f, true);
        // 	else if (AutoVisualize.get() || subrunningTask == 1)
        // 		doVisualize("XML: " + f);
        // }
    }

    // edu.mit.csail.sdg.alloy4whole.SimpleGUI.doVisualize(String) for handling
    // instance visualization links

    private void doVisualize(String arg) {
        log("doVisualize() called with " + arg);
        if (arg.startsWith("CORE: ")) { // CORE: filename
            String filename = Util.canon(arg.substring(6));
            Pair<Set<Pos>,Set<Pos>> hCore;
            // Set<Pos> lCore;
            InputStream is = null;
            ObjectInputStream ois = null;
            try {
                is = new FileInputStream(filename);
                ois = new ObjectInputStream(is);
                hCore = (Pair<Set<Pos>,Set<Pos>>) ois.readObject();
                // lCore = (Set<Pos>) ois.readObject();
                List<Err> errs = Stream.concat(hCore.a.stream().map(pos -> new ErrorWarning(pos, "part of unsat core")), hCore.b.stream().map(pos -> new ErrorWarning(pos, "possibly part of unsat core"))).collect(Collectors.toList());

                List<PublishDiagnosticsParams> publishDiags = this.toPublishDiagnosticsParamsList(errs);

                fileUrisOfLastPublishedDiagnostics.clear();
                fileUrisOfLastPublishedDiagnostics.addAll(publishDiags.stream().map(PublishDiagnosticsParams::getUri).collect(Collectors.toList()));

                publishDiags.forEach(client::publishDiagnostics);

            } catch (Throwable ex) {
                System.err.println("Error reading or parsing the core \"" + filename + "\"\n");
                // return null;
            } finally {
                Util.close(ois);
                Util.close(is);
            }



            // text.clearShade();
            // text.shade(hCore.b, subCoreColor, false);
            // text.shade(hCore.a, coreColor, false);
            // // shade again, because if not all files were open, some shadings
            // // will have no effect
            // text.shade(hCore.b, subCoreColor, false);
            // text.shade(hCore.a, coreColor, false);
        }
        if (arg.startsWith("POS: ")) { // POS: x1 y1 x2 y2 filename
            Scanner s = new Scanner(arg.substring(5));
            int x1 = s.nextInt(), y1 = s.nextInt(), x2 = s.nextInt(), y2 = s.nextInt();
            String f = s.nextLine();
            if (f.length() > 0 && f.charAt(0) == ' ')
                f = f.substring(1); // Get rid of the space after Y2
            Pos p = new Pos(Util.canon(f), x1, y1, x2, y2);

        }
        if (arg.startsWith("CNF: ")) { // CNF: filename
            String filename = Util.canon(arg.substring(5));
            try {
                String text = Util.readAll(filename);
                OurDialog.showtext("Text Viewer", text);
            } catch (IOException ex) {
                System.err.println("Error reading the file \"" + filename + "\"\n");
            }
        }
        if (arg.startsWith("XML: ")) { // XML: filename

            // from SimpleGui
            // VizGUI viz = new VizGUI(false, "", windowmenu2, enumerator, evaluator);
            if (viz == null)
                viz = new VizGUI(false, "", null, enumerator, evaluator, 1);
            viz.loadXML(Util.canon(arg.substring(5)), false);
        }
    }

    /** This object performs solution enumeration. */
    private final Computer  enumerator = new Computer() {

                                           @Override
                                           public String compute(Object input) {
                                               final String[] arg = (String[]) input;
                                               //OurUtil.show(frame);
                                               if (WorkerEngine.isBusy())
                                                   throw new RuntimeException("Alloy4 is currently executing a SAT solver command. Please wait until that command has finished.");
                                               //SimpleCallback1 cb = new SimpleCallback1(SimpleGUI.this, viz, log, VerbosityPref.get().ordinal(), latestAlloyVersionName, latestAlloyVersion);
                                               WorkerCallback cb = getVizWorkerCallback();
                                               SimpleTask2 task = new SimpleTask2();
                                               task.filename = arg[0];
                                               task.index = Integer.valueOf(arg[1]);
                                               try {
                                                   if (AlloyCore.isDebug())
                                                       WorkerEngine.runLocally(task, cb);
                                                   else
                                                       WorkerEngine.run(task, SubMemory.get(), SubStack.get(), SimpleGUI.alloyHome(null) + fs + "binary", "", cb);
                                                   // task.run(cb);
                                               } catch (Throwable ex) {
                                                   WorkerEngine.stop();
                                                   System.err.println("Fatal Error: Solver failed due to unknown reason.\n" + "One possible cause is that, in the Options menu, your specified\n" + "memory size is larger than the amount allowed by your OS.\n" + "Also, please make sure \"java\" is in your program path.\n");
                                                   //log.logBold("Fatal Error: Solver failed due to unknown reason.\n" + "One possible cause is that, in the Options menu, your specified\n" + "memory size is larger than the amount allowed by your OS.\n" + "Also, please make sure \"java\" is in your program path.\n");
                                                   //log.logDivider();
                                                   //log.flush();
                                                   doStop(2);
                                                   return arg[0];
                                               }
                                                                                                                                                                                                                                                                                                                                     /*
                                                                                                                                                                                                                                                                                                                                      * subrunningTask
                                                                                                                                                                                                                                                                                                                                      * =
                                                                                                                                                                                                                                                                                                                                      * 2;
                                                                                                                                                                                                                                                                                                                                      * runmenu
                                                                                                                                                                                                                                                                                                                                      * .
                                                                                                                                                                                                                                                                                                                                      * setEnabled
                                                                                                                                                                                                                                                                                                                                      * (
                                                                                                                                                                                                                                                                                                                                      * false
                                                                                                                                                                                                                                                                                                                                      * )
                                                                                                                                                                                                                                                                                                                                      * ;
                                                                                                                                                                                                                                                                                                                                      * runbutton
                                                                                                                                                                                                                                                                                                                                      * .
                                                                                                                                                                                                                                                                                                                                      * setVisible
                                                                                                                                                                                                                                                                                                                                      * (
                                                                                                                                                                                                                                                                                                                                      * false
                                                                                                                                                                                                                                                                                                                                      * )
                                                                                                                                                                                                                                                                                                                                      * ;
                                                                                                                                                                                                                                                                                                                                      * showbutton
                                                                                                                                                                                                                                                                                                                                      * .
                                                                                                                                                                                                                                                                                                                                      * setEnabled
                                                                                                                                                                                                                                                                                                                                      * (
                                                                                                                                                                                                                                                                                                                                      * false
                                                                                                                                                                                                                                                                                                                                      * )
                                                                                                                                                                                                                                                                                                                                      * ;
                                                                                                                                                                                                                                                                                                                                      * stopbutton
                                                                                                                                                                                                                                                                                                                                      * .
                                                                                                                                                                                                                                                                                                                                      * setVisible
                                                                                                                                                                                                                                                                                                                                      * (
                                                                                                                                                                                                                                                                                                                                      * true
                                                                                                                                                                                                                                                                                                                                      * )
                                                                                                                                                                                                                                                                                                                                      * ;
                                                                                                                                                                                                                                                                                                                                      */
                                               return arg[0];
                                           }
                                       };


    /** This object performs expression evaluation. */
    private static Computer evaluator  = new Computer() {

                                           private String filename = null;

                                           @Override
                                           public final Object compute(final Object input) throws Exception {
                                               if (input instanceof File) {
                                                   filename = ((File) input).getAbsolutePath();
                                                   return "";
                                               }
                                               if (!(input instanceof String[]))
                                                   return "";
                                               final String[] strs = (String[]) input;
                                               if (strs[0].trim().length() == 0)
                                                   return ""; // Empty line
                                               Module root = null;
                                               A4Solution ans = null;
                                               try {
                                                   Map<String,String> fc = new LinkedHashMap<String,String>();
                                                   XMLNode x = new XMLNode(new File(filename));
                                                   if (!x.is("alloy"))
                                                       throw new Exception();
                                                   String mainname = null;
                                                   for (XMLNode sub : x)
                                                       if (sub.is("instance")) {
                                                           mainname = sub.getAttribute("filename");
                                                           break;
                                                       }
                                                   if (mainname == null)
                                                       throw new Exception();
                                                   for (XMLNode sub : x)
                                                       if (sub.is("source")) {
                                                           String name = sub.getAttribute("filename");
                                                           String content = sub.getAttribute("content");
                                                           fc.put(name, content);
                                                       }
                                                   root = CompUtil.parseEverything_fromFile(A4Reporter.NOP, fc, mainname, (Version.experimental && ImplicitThis.get()) ? 2 : 1);
                                                   ans = A4SolutionReader.read(root.getAllReachableSigs(), x);
                                                   for (ExprVar a : ans.getAllAtoms()) {
                                                       root.addGlobal(a.label, a);
                                                   }
                                                   for (ExprVar a : ans.getAllSkolems()) {
                                                       root.addGlobal(a.label, a);
                                                   }
                                               } catch (Throwable ex) {
                                                   throw new ErrorFatal("Failed to read or parse the XML file.");
                                               }
                                               try {
                                                   Expr e = CompUtil.parseOneExpression_fromString(root, strs[0]);
                                                   if (AlloyCore.isDebug() && VerbosityPref.get() == Verbosity.FULLDEBUG) {
                                                       SimInstance simInst = SimpleGUI.convert(root, ans);
                                                       if (simInst.wasOverflow())
                                                           return simInst.visitThis(e).toString() + " (OF)";
                                                   }
                                                   return ans.eval(e, Integer.valueOf(strs[1])).toString();
                                               } catch (Exception ex) {
                                                   throw new ErrorType("Parsing ", ex);
                                               }
                                           }
                                       };

    static Pos getCurrentWordSelectionAsPos(String text, Pos pos) {
        int[] sel = getCurrentWordSelection(text, pos);
        pos = Pos.toPos(text, sel[0], sel[1]);
        return pos;
    }

    // from OurSyntaxWidget
    static int[] getCurrentWordSelection(String text, Pos pos) {

        int[] startEnd = pos.toStartEnd(text);
        int selectionStart = startEnd[0];
        int selectionEnd = startEnd[1];

        if (!isValidSelection(text, selectionStart, selectionEnd))
            return null;

        while (isValidSelection(text, selectionStart - 1, selectionEnd) && inWord(text.charAt(selectionStart - 1)))
            selectionStart--;

        while (isValidSelection(text, selectionStart, selectionEnd + 1) && inWord(text.charAt(selectionEnd)))
            selectionEnd++;

        if (!isValidSelection(text, selectionStart, selectionEnd))
            return null;
        return new int[] {
                          selectionStart, selectionEnd
        };
    }

    // from OurSyntaxWidget
    static boolean isValidSelection(String text, int start, int end) {
        return start >= 0 && start <= end && end >= start && end <= text.length();
    }

    // from OurSyntaxWidget
    private static boolean inWord(char c) {
        return Character.isAlphabetic(c) || Character.isDigit(c) || Character.isIdentifierIgnorable(c) || Character.isJavaIdentifierPart(c) || c == '\'' || c == '"';
    }


    private static void log(String s) {
        System.err.println("thread: " + Thread.currentThread().getId() + "| " + s);
    }


    static List<Expr> findAllReferences(CompModule module, Pos pos, boolean includeSelf) {

        List<Expr> references = new ArrayList<Expr>();

        if (module == null)
            return references;
        Expr expr = module.find(pos);
        if (expr == null)
            return references;
        Expr referencedExpr = expr.referenced() != null ? module.find(expr.referenced().pos()) : expr;


        if (includeSelf)
            references.add(referencedExpr);
        module.visitExpressionsResilient(new VisitQueryOnce<Void>() {

            @Override
            public boolean visited(Expr expr) {
                boolean visited = super.visited(expr);
                if (visited)
                    return visited;

                if (expr.referenced() != null && expr.referenced().pos().equals(referencedExpr.pos)) {
                    log("reference: " + expr.toString());
                    references.add(expr);
                }
                return visited;
            }
        });
        return references;
    }

    List<Pos> findAllReferencesGlobally(CompModule module, Pos pos, String rootDir, boolean includeSelf, boolean continueOnError) throws Err {

        List<Pos> references = new ArrayList<Pos>();

        Expr expr = module.find(pos);

        log("finding references to " + pos.toRangeString() + ", expr: " + expr);

        if (expr == null)
            return references;

        if (expr.referenced() != null)
            log("expr.referenced(): " + expr.referenced().toString());


        Pos targetPos = expr.referenced() != null ? expr.referenced().pos() : expr.pos;
        log("targetPos: " + targetPos.toRangeString());

        if (targetPos.equals(Pos.UNKNOWN))
            return references;

        if (includeSelf)
            references.add(targetPos);

        for (File child : alloyFilesInDir(rootDir)) {

            String filePath = fileUriToPath(child.toURI().toString());
            try {
                CompModule childModule = getCompModuleForFileUri(child.toURI().toString());

                childModule.visitExpressionsResilient(new VisitQueryOnce<Void>() {

                    @Override
                    public boolean visited(Expr expr) {
                        boolean visited = super.visited(expr);
                        if (visited)
                            return visited;

                        if (expr.referenced() != null) {
                            Pos rpos = expr.referenced().pos();
                            if (rpos.equals(targetPos)) {
                                log("reference: " + expr.toString() + "; to file: " + rpos.filename);
                                references.add(expr.pos);
                            }
                        }
                        return visited;
                    }
                });
            } catch (Exception ex) {
                log("exception parsing" + child.toString() + ": " + ex.toString());
                if (!continueOnError)
                    throw ex;
            }
        }
        return references;
    }

    static List<File> alloyFilesInDir(String dir) {
        File[] directoryListing = new File(dir).listFiles();
        return Arrays.stream(directoryListing).filter(child -> child.isFile() && (FilenameUtils.isExtension(child.getAbsolutePath(), new String[] {
                                                                                                                                                   "als"
        }) || isAlloyMarkdownFile(child.getAbsolutePath()))).collect(Collectors.toList());
    }

    static boolean isAlloyMarkdownFile(String filename) {
        if (!FilenameUtils.isExtension(filename, new String[] {
                                                               "md"
        }))
            return false;

        try (BufferedReader br = new BufferedReader(new FileReader(filename))) {
            return "---".equals(br.readLine());
        } catch (IOException ex) {
            return false;
        }
    }

    static boolean isAlloyFile(String filename, String contents) {
        if (FilenameUtils.isExtension(filename, new String[] {
                                                              "als"
        }) || (FilenameUtils.isExtension(filename, new String[] {
                                                              "md"
        }) && contents.startsWith("---")))
            return true;

        return false;
    }


}