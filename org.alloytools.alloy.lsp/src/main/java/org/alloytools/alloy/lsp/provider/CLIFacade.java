package org.alloytools.alloy.lsp.provider;

import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.getopt.Arguments;
import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;

@AlloyMain(
           name = {
                   "lsp"
           } )
public class CLIFacade {

    @Description("Language Server for Alloy. " )
    @Arguments(
               arg = "[port]" )
    interface LSPOptions extends Options {

    }

    public void _lsp(LSPOptions options) throws Exception {
        AlloyLanguageServer.main(options._arguments().toArray(new String[0]));
    }

}