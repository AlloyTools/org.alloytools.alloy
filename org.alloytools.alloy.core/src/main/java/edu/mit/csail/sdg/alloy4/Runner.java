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

package edu.mit.csail.sdg.alloy4;

import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import javax.swing.AbstractAction;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.MenuEvent;
import javax.swing.event.MenuListener;

/**
 * This class converts a Runnable into an AbstractAction, WindowListener,
 * CaretListener, and MenuListener also.
 */

public abstract class Runner extends AbstractAction implements Runnable, WindowListener, MenuListener, CaretListener, FocusListener {

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /**
     * Constructs a new runner; you should override the run() and run(arg) method to
     * customize it.
     */
    public Runner() {}

    /**
     * This method should be overriden to provide the default action that this
     * Runner would perform.
     */
    @Override
    public abstract void run();

    /**
     * This method should be overriden to provide the default action that this
     * Runner would perform given an argument.
     */
    public abstract void run(Object arg);

    /**
     * This method is defined in java.awt.event.ActionListener; (this implementation
     * calls this.run())
     */
    @Override
    public final void actionPerformed(ActionEvent e) {
        run();
    }

    /**
     * This method is defined in javax.swing.event.MenuListener; (this
     * implementation calls this.run())
     */
    @Override
    public final void menuSelected(MenuEvent e) {
        run();
    }

    /**
     * This method is defined in javax.swing.event.MenuListener; (this
     * implementation does nothing)
     */
    @Override
    public final void menuDeselected(MenuEvent e) {}

    /**
     * This method is defined in javax.swing.event.MenuListener; (this
     * implementation does nothing)
     */
    @Override
    public final void menuCanceled(MenuEvent e) {}

    /**
     * This method is defined in java.awt.event.CaretListener; (this implementation
     * calls this.run())
     */
    @Override
    public final void caretUpdate(CaretEvent e) {
        run();
    }

    /**
     * This method is defined in java.awt.event.FocusListener; (this implementation
     * calls this.run())
     */
    @Override
    public final void focusGained(FocusEvent e) {
        run();
    }

    /**
     * This method is defined in java.awt.event.FocusListener; (this implementation
     * does nothing)
     */
    @Override
    public final void focusLost(FocusEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * calls this.run())
     */
    @Override
    public final void windowClosing(WindowEvent e) {
        run();
    }

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowClosed(WindowEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowOpened(WindowEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowIconified(WindowEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowDeiconified(WindowEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowActivated(WindowEvent e) {}

    /**
     * This method is defined in java.awt.event.WindowListener; (this implementation
     * does nothing)
     */
    @Override
    public final void windowDeactivated(WindowEvent e) {}

    /**
     * This helper method returns a Runnable whose run() method will call
     * window.dispose()
     */
    public static final Runner createDispose(final Window window) {
        return new Runner() {

            private static final long serialVersionUID = 0;

            @Override
            public final void run() {
                window.dispose();
            }

            @Override
            public final void run(Object arg) {
                window.dispose();
            }
        };
    }
}
