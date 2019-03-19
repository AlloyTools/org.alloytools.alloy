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

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Event;
import java.awt.Font;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.swing.AbstractAction;
import javax.swing.JPanel;
import javax.swing.JScrollBar;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.KeyStroke;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Caret;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;

import org.alloytools.graphics.util.AlloyGraphics;
import org.alloytools.util.table.Table;

/**
 * Graphical input/output prompt.
 * <p>
 * This class's constructor takes a Computer object, then constructs a
 * JScrollPane in which the user can type commands, and the output from the
 * Computer object will be displayed. Empty input lines are ignored. This
 * interactive prompt supports UP and DOWN arrow command histories and basic
 * copy/cut/paste editing.
 * <p>
 * For each user input, if the Computer object returns a String, it is displayed
 * in blue. But if the Computer object throws an exception, the exception will
 * be displayed in red.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class OurConsole extends JScrollPane {

    final static int                  menuShortcutKeyMask = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();

    /** This ensures the class can be serialized reliably. */
    private static final long         serialVersionUID    = 0;

    /** The style for default text. */
    private final static AttributeSet plain               = style("Verdana,Helvetica", 14, false, false, false, Color.BLACK, 0);

    /** The style for table text. */
    private final static AttributeSet mono                = style("Input Mono,DejaVu Sans Mono,Courier New,Courier", 14, false, false, false, Color.BLACK, 10);

    /** The style for bold text. */
    private final static AttributeSet bold                = style("Verdana,Helvetica", 14, true, false, false, Color.BLACK, 0);

    /** The style for successful result. */
    private final static AttributeSet good                = style("Verdana,Helvetica", 14, false, false, false, Color.BLUE, 10);

    /** The style for failed result. */
    private final static AttributeSet bad                 = style("Verdana,Helvetica", 14, false, false, false, Color.RED, 10);

    /**
     * The number of characters that currently exist above the horizontal divider
     * bar. (The interactive console is composed of a JTextPane which contains 0 or
     * more input/output pairs, followed by a horizontal divider bar, followed by an
     * embedded sub-JTextPane (where the user can type in the next input))
     */
    private int                       len                 = 0;

    /**
     * The main JTextPane containing 0 or more input/output pairs, followed by a
     * horizontal bar, followed by this.sub
     */
    private final JTextPane           main                = do_makeTextPane(false, 5, 5, 5);

    /**
     * The sub JTextPane where the user can type in the next command.
     */
    private final JTextPane           sub                 = do_makeTextPane(true, 10, 10, 0);

    /**
     * The history of all commands entered so far, plus an extra String representing
     * the user's next command.
     */
    private final List<String>        history             = new ArrayList<String>();
    {
        history.add("");
    }

    /**
     * The position in this.history that is currently showing.
     */
    private int browse = 0;

    /*
     * Helper method that construct a mutable style with the given font name, font
     * size, boldness, color, and left indentation.
     */
    static MutableAttributeSet style(String fontName, int fontSize, boolean boldness, boolean italic, boolean strike, Color color, int leftIndent) {


        fontName = AlloyGraphics.matchBestFontName(fontName);

        MutableAttributeSet s = new SimpleAttributeSet();
        StyleConstants.setFontFamily(s, fontName);
        StyleConstants.setFontSize(s, fontSize);
        StyleConstants.setLineSpacing(s, -0.2f);
        StyleConstants.setBold(s, boldness);
        StyleConstants.setItalic(s, italic);
        StyleConstants.setForeground(s, color);
        StyleConstants.setLeftIndent(s, leftIndent);
        StyleConstants.setStrikeThrough(s, strike);
        return s;
    }

    /**
     * Construct a JScrollPane that allows the user to interactively type in
     * commands and see replies.
     *
     * @param computer - this object is used to evaluate the user input
     * @param syntaxHighlighting - if true, the "input area" will be
     *            syntax-highlighted
     * @param initialMessages - this is a list of String and Boolean; each String is
     *            printed to the screen as is, and Boolean.TRUE will turn subsequent
     *            text bold, and Boolean.FALSE will turn subsequent text non-bold.
     */
    public OurConsole(final Computer computer, boolean syntaxHighlighting, Object... initialMessages) {
        super(VERTICAL_SCROLLBAR_AS_NEEDED, HORIZONTAL_SCROLLBAR_AS_NEEDED);
        if (syntaxHighlighting) {
            sub.setDocument(new OurSyntaxUndoableDocument("Verdana", 14));
        }
        setViewportView(main);
        // show the initial message
        AttributeSet st = plain;
        for (Object x : initialMessages) {
            if (x instanceof Boolean)
                st = (Boolean.TRUE.equals(x) ? bold : plain);
            else
                do_add(-1, String.valueOf(x), st);
        }
        do_add(-1, "\n", plain); // we must add a linebreak to ensure that
                                // subsequent text belong to a "different
                                // paragraph"
                                // insert the divider and the sub JTextPane
        StyledDocument doc = main.getStyledDocument();
        JPanel divider = new JPanel();
        divider.setBackground(Color.LIGHT_GRAY);
        divider.setPreferredSize(new Dimension(1, 1));
        MutableAttributeSet dividerStyle = new SimpleAttributeSet();
        StyleConstants.setComponent(dividerStyle, divider);
        MutableAttributeSet inputStyle = new SimpleAttributeSet();
        StyleConstants.setComponent(inputStyle, sub);
        len = doc.getLength();
        do_add(-1, " \n", dividerStyle); // The space character won't be
                                        // displayed; it will instead be
                                        // drawn as a divider
        do_add(-1, " \n", inputStyle); // The space character won't be
                                      // displayed; it will instead display
                                      // the input buffer
        final Caret subCaret = sub.getCaret(), mainCaret = main.getCaret();
        // When caret moves in the sub JTextPane, we cancel any active selection
        // in the main JTextPane
        subCaret.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                if (mainCaret.getMark() != mainCaret.getDot())
                    mainCaret.setDot(mainCaret.getDot());
            }
        });
        // When caret moves in the main JTextPane, we cancel any active
        // selection in the sub JTextPane
        mainCaret.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                if (subCaret.getMark() != subCaret.getDot())
                    subCaret.setDot(subCaret.getDot());
            }
        });
        // now, create the paste/copy/cut actions
        AbstractAction alloy_paste = new AbstractAction("alloy_paste") {

            static final long serialVersionUID = 0;

            @Override
            public void actionPerformed(ActionEvent x) {
                sub.paste();
            }
        };
        AbstractAction alloy_copy = new AbstractAction("alloy_copy") {

            static final long serialVersionUID = 0;

            @Override
            public void actionPerformed(ActionEvent x) {
                System.out.println("copy");
                if (sub.getSelectionStart() != sub.getSelectionEnd())
                    sub.copy();
                else
                    main.copy();
            }
        };
        AbstractAction alloy_cut = new AbstractAction("alloy_cut") {

            static final long serialVersionUID = 0;

            @Override
            public void actionPerformed(ActionEvent x) {
                if (sub.getSelectionStart() != sub.getSelectionEnd())
                    sub.cut();
                else
                    main.copy();
            }
        };
        // create the keyboard associations: ctrl-{c,v,x,insert} and
        // shift-{insert,delete}
        for (JTextPane x : Arrays.asList(main, sub)) {
            x.getActionMap().put("alloy_paste", alloy_paste);
            x.getActionMap().put("alloy_copy", alloy_copy);
            x.getActionMap().put("alloy_cut", alloy_cut);
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_V, menuShortcutKeyMask), "alloy_paste");
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_C, menuShortcutKeyMask), "alloy_copy");
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_X, menuShortcutKeyMask), "alloy_cut");
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, Event.SHIFT_MASK), "alloy_paste");
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, Event.CTRL_MASK), "alloy_copy");
            x.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, Event.SHIFT_MASK), "alloy_cut");
        }
        // configure so that, upon receiving focus, we automatically focus and
        // scroll to the sub-JTextPane
        FocusAdapter focus = new FocusAdapter() {

            @Override
            public void focusGained(FocusEvent e) {
                sub.requestFocusInWindow();
                sub.scrollRectToVisible(new Rectangle(0, sub.getY(), 1, sub.getHeight()));
            }
        };
        addFocusListener(focus);
        sub.addFocusListener(focus);
        main.addFocusListener(focus);
        // configure so that mouse clicks in the main JTextPane will immediately
        // transfer focus to the sub JTextPane
        main.addMouseListener(new MouseAdapter() {

            @Override
            public void mousePressed(MouseEvent e) {
                sub.requestFocusInWindow();
            }

            @Override
            public void mouseClicked(MouseEvent e) {
                sub.requestFocusInWindow();
            }
        });
        // configure the behavior for PAGE_UP, PAGE_DOWN, UP, DOWN, TAB, and
        // ENTER
        sub.addKeyListener(new KeyListener() {

            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyChar() == '\t') {
                    e.consume();
                }
                if (e.getKeyChar() == '\n') {
                    e.consume();
                    String cmd = sub.getText();
                    sub.setText("");
                    do_command(computer, cmd);
                }
            }

            @Override
            public void keyPressed(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER || e.getKeyCode() == KeyEvent.VK_TAB)
                    e.consume();
                if (e.getKeyCode() == KeyEvent.VK_PAGE_UP) {
                    e.consume();
                    do_pageup();
                }
                if (e.getKeyCode() == KeyEvent.VK_PAGE_DOWN) {
                    e.consume();
                    do_pagedown();
                }
                if (e.getKeyCode() == KeyEvent.VK_UP) {
                    e.consume();
                    if (browse == history.size() - 1) {
                        history.set(browse, sub.getText());
                    }
                    if (browse > 0 && browse - 1 < history.size()) {
                        browse--;
                        sub.setText(history.get(browse));
                    }
                }
                if (e.getKeyCode() == KeyEvent.VK_DOWN) {
                    e.consume();
                    if (browse < history.size() - 1) {
                        browse++;
                        sub.setText(history.get(browse));
                    }
                }
            }

            @Override
            public void keyReleased(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER || e.getKeyCode() == KeyEvent.VK_TAB)
                    e.consume();
            }
        });
    }

    /**
     * This helper method constructs a JTextPane with the given settings.
     */
    private static JTextPane do_makeTextPane(boolean editable, int topMargin, int bottomMargin, int otherMargin) {
        JTextPane x = OurAntiAlias.pane(null, Color.BLACK, Color.WHITE, new Font("Verdana", Font.PLAIN, 14));
        x.setEditable(editable);
        x.setAlignmentX(0);
        x.setAlignmentY(0);
        x.setCaretPosition(0);
        x.setMargin(new Insets(topMargin, otherMargin, bottomMargin, otherMargin));
        return x;
    }

    /** This method processes a user command. */
    private void do_command(Computer computer, String cmd) {
        cmd = cmd.trim();
        if (cmd.length() == 0)
            return;

        cmd = TableView.revertSuffix(cmd);
        StyledDocument doc = main.getStyledDocument();
        if (history.size() >= 2 && cmd.equals(history.get(history.size() - 2))) {
            // If the user merely repeated the most recent command, then don't
            // grow the history
            history.set(history.size() - 1, "");
        } else {
            // Otherwise, grow the history
            history.set(history.size() - 1, cmd);
            history.add("");
        }
        browse = history.size() - 1;
        // display the command
        int old = doc.getLength();
        do_add(len, cmd + "\n\n", plain);
        len += (doc.getLength() - old);
        // perform the computation
        boolean isBad = false;
        Object result;
        try {
            result = computer.compute(cmd);
        } catch (Throwable ex) {
            result = ex.toString();
            isBad = true;
        }
        int savePosition = len;
        // display the outcome
        old = doc.getLength();
        do_add(len, result.toString().trim() + "\n\n", (isBad ? bad : good));
        len += (doc.getLength() - old);
        // indent the outcome
        main.setSelectionStart(savePosition + 1);
        main.setSelectionEnd(len);
        main.setParagraphAttributes(good, false);
        // redraw then scroll to the bottom
        invalidate();
        repaint();
        validate();
        sub.scrollRectToVisible(new Rectangle(0, sub.getY(), 1, sub.getHeight()));
        do_pagedown(); // need to do this after the validate() so that the
                      // scrollbar knows the new limit
    }

    /** Performs "page up" in the JScrollPane. */
    private void do_pageup() {
        JScrollBar bar = getVerticalScrollBar();
        bar.setValue(bar.getValue() - 200);
    }

    /** Performs "page down" in the JScrollPane. */
    private void do_pagedown() {
        JScrollBar bar = getVerticalScrollBar();
        bar.setValue(bar.getValue() + 200);
    }

    /**
     * Insert the given text into the given location and with the given style if
     * where>=0; append the text if where<0.
     */
    private void do_add(int where, String text, AttributeSet style) {
        try {
            StyledDocument doc = main.getStyledDocument();
            if (TableView.isTable(text)) {
                Table table = TableView.toTable(text, false);

                doc.insertString(where >= 0 ? where : doc.getLength(), table.toString(), mono);
                main.getCaret().setSelectionVisible(false);
            } else
                doc.insertString(where >= 0 ? where : doc.getLength(), text, style);
        } catch (BadLocationException ex) {}
    }
}
