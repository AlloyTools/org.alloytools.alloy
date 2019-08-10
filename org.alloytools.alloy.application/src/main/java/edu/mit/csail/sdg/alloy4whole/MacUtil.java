/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import javax.swing.SwingUtilities;

import com.apple.eawt.Application;
import com.apple.eawt.ApplicationAdapter;
import com.apple.eawt.ApplicationEvent;
import com.apple.eawt.ApplicationListener;

import edu.mit.csail.sdg.alloy4.Runner;

/**
 * This class provides better integration on Mac OS X.
 * <p>
 * You must not call any methods here if you're not on Mac OS X, since that
 * triggers the loading of com.apple.eawt.* which are not available on other
 * platforms.
 * <p>
 * <b>Thread Safety:</b> Safe.
 */

public final class MacUtil {

    /**
     * Constructor is private, since this class never needs to be instantiated.
     */
    public MacUtil() {
    }

    /** The cached Application object. */
    private Application         app      = null;

    /**
     * The previous ApplicationListener (or null if there was none).
     */
    private ApplicationListener listener = null;

    /**
     * Register a Mac OS X "ApplicationListener"; if there was a previous listener,
     * it will be removed first.
     *
     * @param reopen - when the user clicks on the Dock icon, we'll call
     *            reopen.run() using SwingUtilities.invokeLater
     * @param about - when the user clicks on About Alloy4, we'll call about.run()
     *            using SwingUtilities.invokeLater
     * @param open - when a file needs to be opened, we'll call open.run(filename)
     *            using SwingUtilities.invokeLater
     * @param quit - when the user clicks on Quit, we'll call quit.run() using
     *            SwingUtilities.invokeAndWait
     */
    public synchronized void registerApplicationListener(final Runnable reopen, final Runnable about, final Runner open, final Runnable quit) {
        if (app == null)
            app = new Application();
        else if (listener != null)
            app.removeApplicationListener(listener);
        listener = new ApplicationAdapter() {

            @Override
            public void handleReOpenApplication(ApplicationEvent arg) {
                SwingUtilities.invokeLater(reopen);
            }

            @Override
            public void handleAbout(ApplicationEvent arg) {
                arg.setHandled(true);
                SwingUtilities.invokeLater(about);
            }

            @Override
            public void handleOpenFile(ApplicationEvent arg) {
                final String filename = arg.getFilename();
                SwingUtilities.invokeLater(new Runnable() {

                    @Override
                    public void run() {
                        open.run(filename);
                    }
                });
            }

            @Override
            public void handleQuit(ApplicationEvent arg) {
                try {
                    if (SwingUtilities.isEventDispatchThread())
                        quit.run();
                    else
                        SwingUtilities.invokeAndWait(quit);
                } catch (Throwable e) {
                    // Nothing we can do; we're already trying to quit!
                }
                arg.setHandled(false);
            }
        };
        app.addApplicationListener(listener);
    }

    public void addMenus(SimpleGUI simpleGUI) {
        //        for (Method m : Application.class.getMethods()) {
        //            System.out.println(m);
        //        }
        //        try {
        //            //Application.getApplication().addAboutMenuItem();
        //        } catch (Throwable e) {
        //            System.err.println("cannot add about menus");
        //        }
        try {
            Application.getApplication().addPreferencesMenuItem();
        } catch (Throwable e) {
            System.err.println("cannot add preference menus");
        }
        try {
            Application.getApplication().addApplicationListener(new ApplicationAdapter() {

                @Override
                public void handlePreferences(ApplicationEvent ae) {
                    simpleGUI.doPreferences();
                }

            });
        } catch (Throwable e) {
            System.err.println("cannot add app listener");
        }
    }
}
