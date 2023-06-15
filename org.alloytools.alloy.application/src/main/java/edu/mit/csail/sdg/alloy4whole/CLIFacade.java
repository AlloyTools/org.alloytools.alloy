package edu.mit.csail.sdg.alloy4whole;

import javax.swing.SwingUtilities;

import org.alloytools.alloy.infrastructure.api.AlloyMain;

import aQute.lib.getopt.Description;
import aQute.lib.getopt.Options;


@AlloyMain
public class CLIFacade {

    interface GuiOptions extends Options {

    }

    @Description("Opens up the Graphic User Interface of Alloy" )
    public void _gui(GuiOptions options) {
        SwingUtilities.invokeLater(new Runnable() {

            @Override
            public void run() {
                new SimpleGUI(options._arguments().toArray(new String[0]));
            }
        });

    }

    @Override
    public String toString() {
        return "GUI";
    }
}

