package org.alloytools.alloy.lsp.provider;

import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;

@AlloyMain
public class CLIFacade {

    @Description("Language Server for Alloy. " )
    @Arguments(
               arg = "[port]" )
    interface LSPOptions extends Options {

    }

    @Description("Language Server for Alloy. " )
    public void _lsp(LSPOptions options) throws Exception {
        AlloyLanguageServer.main(options._arguments().toArray(new String[0]));
    }

    @Description("Language Server for Alloy. " )
    public void _ls(LSPOptions options) throws Exception {
        AlloyLanguageServer.main(options._arguments().toArray(new String[0]));
    }

    @Override
    public String toString() {
        return "LSP";
    }

}
