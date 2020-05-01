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
import java.awt.Frame;
import java.awt.event.ActionEvent;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.io.File;
import java.util.Collection;
import java.util.Date;
import java.util.Objects;

import javax.swing.AbstractAction;
import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.KeyStroke;
import javax.swing.border.EmptyBorder;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.AbstractDocument;
import javax.swing.text.BadLocationException;
import javax.swing.text.BoxView;
import javax.swing.text.Document;
import javax.swing.text.Element;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.View;
import javax.swing.text.ViewFactory;

import edu.mit.csail.sdg.alloy4.Listener.Event;
import edu.mit.csail.sdg.ast.Clause;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBad;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;

/**
 * Graphical syntax-highlighting editor.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread
 */

public final class OurSyntaxWidget {

    /**
     * The current list of listeners; possible events are { STATUS_CHANGE, FOCUSED,
     * CTRL_PAGE_UP, CTRL_PAGE_DOWN, CARET_MOVED }.
     */
    public final Listeners                  listeners        = new Listeners();

    /** The JScrollPane containing everything. */
    private final JScrollPane               component        = OurUtil.make(new JScrollPane(), new EmptyBorder(0, 0, 0, 0));

    /** This is an optional JComponent annotation. */
    public final JComponent                 obj1;

    /** This is an optional JComponent annotation. */
    public final JComponent                 obj2;

    /**
     * The underlying StyledDocument being displayed (changes will trigger the
     * STATUS_CHANGE event)
     */
    private final OurSyntaxUndoableDocument doc              = new OurSyntaxUndoableDocument("Monospaced", 14);

    /** The underlying JTextPane being displayed. */
    private final JTextPane                 pane             = OurAntiAlias.pane(this::getTooltip, Color.BLACK, Color.WHITE, new EmptyBorder(6, 6, 6, 6));

    /**
     * The filename for this JTextPane (changes will trigger the STATUS_CHANGE
     * event)
     */
    private String                          filename         = "";

    /**
     * the file modification date for the file loaded. If no file is loaded
     * (!isFile), this must be -1.
     */
    private long                            fileModifiedDate = -1;

    /**
     * Whether this JTextPane has been modified since last load/save (changes will
     * trigger the STATUS_CHANGE event)
     */
    private boolean                         modified;

    /**
     * Whether this JTextPane corresponds to an existing disk file (changes will
     * trigger the STATUS_CHANGE event)
     */
    private boolean                         isFile;

    /** Caches the most recent background painter if nonnull. */
    private OurHighlighter                  painter;

    private OurTabbedSyntaxWidget           parent;

    private volatile CompModule             module;

    /**
     * Constructs a syntax-highlighting widget.
     */
    public OurSyntaxWidget(OurTabbedSyntaxWidget parent) {
        this(parent, true, "", "Monospaced", 14, 4, null, null);
    }

    /**
     * Constructs a syntax-highlighting widget.
     *
     * @param parent
     */
    @SuppressWarnings("serial" )
    public OurSyntaxWidget(OurTabbedSyntaxWidget parent, boolean enableSyntax, String text, String fontName, int fontSize, int tabSize, JComponent obj1, JComponent obj2) {
        pane.addKeyListener(new KeyListener() {

            @Override
            public void keyTyped(KeyEvent e) {
                module = null;
            }

            @Override
            public void keyReleased(KeyEvent e) {
                module = null;
            }

            @Override
            public void keyPressed(KeyEvent e) {
                module = null;
            }
        });
        this.parent = parent;
        this.obj1 = obj1;
        this.obj2 = obj2;
        final OurSyntaxWidget me = this;
        final ViewFactory defaultFactory = (new StyledEditorKit()).getViewFactory();
        doc.do_enableSyntax(enableSyntax);
        doc.do_setFont(fontName, fontSize, tabSize);
        pane.setEditorKit(new StyledEditorKit() { // Prevents line-wrapping up
                                                 // to width=30000, and tells
                                                 // it to use our Document
                                                 // obj

            @Override
            public Document createDefaultDocument() {
                return doc;
            }

            @Override
            public ViewFactory getViewFactory() {
                return new ViewFactory() {

                    @Override
                    public View create(Element x) {
                        if (!AbstractDocument.SectionElementName.equals(x.getName()))
                            return defaultFactory.create(x);
                        return new BoxView(x, View.Y_AXIS) { // 30000 is a good
                                                            // width to use
                                                            // here; value >
                                                            // 32767 appears
                                                            // to cause
                                                            // errors

                            @Override
                            public final float getMinimumSpan(int axis) {
                                return super.getPreferredSpan(axis);
                            }

                            @Override
                            public final void layout(int w, int h) {
                                try {
                                    super.layout(30000, h);
                                } catch (Throwable ex) {
                                }
                            }
                        };
                    }
                };
            }
        });
        if (text.length() > 0) {
            pane.setText(text);
            pane.setCaretPosition(0);
        }
        doc.do_clearUndo();
        pane.getActionMap().put("alloy_copy", new AbstractAction("alloy_copy") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.copy();
            }
        });
        pane.getActionMap().put("alloy_cut", new AbstractAction("alloy_cut") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.cut();
            }
        });
        pane.getActionMap().put("alloy_paste", new AbstractAction("alloy_paste") {

            @Override
            public void actionPerformed(ActionEvent e) {
                pane.paste();
            }
        });
        pane.getActionMap().put("alloy_ctrl_pageup", new AbstractAction("alloy_ctrl_pageup") {

            @Override
            public void actionPerformed(ActionEvent e) {
                listeners.fire(me, Event.CTRL_PAGE_UP);
            }
        });
        pane.getActionMap().put("alloy_ctrl_pagedown", new AbstractAction("alloy_ctrl_pagedown") {

            @Override
            public void actionPerformed(ActionEvent e) {
                listeners.fire(me, Event.CTRL_PAGE_DOWN);
            }
        });
        pane.getActionMap().put("alloy_tab_insert", new AbstractAction("alloy_tab_insert") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doTabInsert();
            }

        });
        pane.getActionMap().put("alloy_tab_remove", new AbstractAction("alloy_tab_remove") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doTabRemove();
            }

        });

        pane.getActionMap().put("alloy-comment-block", new AbstractAction("alloy-comment-block") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doComment();
            }
        });
        pane.getActionMap().put("alloy-nav", new AbstractAction("alloy-comment-block") {

            @Override
            public void actionPerformed(ActionEvent e) {
                doNav();
            }
        });
        pane.getActionMap().put("select-word", getSelectWordAction());

        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_F3, 0), "alloy-nav");
        pane.getInputMap().put(KeyStroke.getKeyStroke('/', OurConsole.menuShortcutKeyMask), "alloy-comment-block");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, 0), "alloy_tab_insert");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, InputEvent.SHIFT_DOWN_MASK), "alloy_tab_remove");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.CTRL_MASK), "alloy_copy");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.CTRL_MASK), "alloy_cut");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_V, InputEvent.CTRL_MASK), "alloy_paste");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.CTRL_MASK), "alloy_copy");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.SHIFT_MASK), "alloy_paste");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, InputEvent.SHIFT_MASK), "alloy_cut");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_UP, InputEvent.CTRL_MASK), "alloy_ctrl_pageup");
        pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_DOWN, InputEvent.CTRL_MASK), "alloy_ctrl_pagedown");
        doc.addDocumentListener(new DocumentListener() {

            @Override
            public void insertUpdate(DocumentEvent e) {
                modified = true;
                listeners.fire(me, Event.STATUS_CHANGE);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                modified = true;
                listeners.fire(me, Event.STATUS_CHANGE);
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
            }
        });
        pane.addFocusListener(new FocusAdapter() {

            @Override
            public void focusGained(FocusEvent e) {
                listeners.fire(me, Event.FOCUSED);
            }
        });
        pane.addCaretListener(new CaretListener() {

            @Override
            public void caretUpdate(CaretEvent e) {
                listeners.fire(me, Event.CARET_MOVED);
            }
        });
        component.addFocusListener(new FocusAdapter() {

            @Override
            public void focusGained(FocusEvent e) {
                pane.requestFocusInWindow();
            }
        });
        component.setFocusable(false);
        component.setMinimumSize(new Dimension(50, 50));
        component.setViewportView(pane);
        modified = false;
    }

    private boolean inWord(char c) {
        return Character.isAlphabetic(c) || Character.isDigit(c) || Character.isIdentifierIgnorable(c) || Character.isJavaIdentifierPart(c) || c == '\'' || c == '"';
    }

    boolean isValidSelection(String text, int start, int end) {
        return start >= 0 && start <= end && end >= start && end <= text.length();
    }

    String getCurrentWord() {
        String text = pane.getText();
        int[] selection = getCurrentWordSelection(text);
        if (selection == null)
            return null;

        return text.substring(selection[0], selection[1]);
    }

    int[] getCurrentWordSelection(String text) {

        int selectionStart = pane.getSelectionStart();
        int selectionEnd = pane.getSelectionEnd();

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

    private AbstractAction getSelectWordAction() {
        return new AbstractAction("select-word") {

            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                String text = pane.getText();
                int[] selection = getCurrentWordSelection(text);
                if (selection == null)
                    return;

                pane.setSelectionStart(selection[0]);
                pane.setSelectionEnd(selection[1]);

            }
        };
    }

    private void doTabInsert() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            sb.insert(0, '\t');
            for (int i = 1; i < sb.length() - 1; i++) {
                char c = sb.charAt(i);
                if (c == '\n') {
                    sb.insert(++i, '\t');
                }
            }
            replaceSelection(sb);
        } else {
            try {
                pane.getDocument().insertString(pane.getCaretPosition(), "\t", null);
            } catch (BadLocationException e1) {
                throw new RuntimeException(e1);
            }
        }
        listeners.fire(this, Event.CARET_MOVED);
    }

    private void doTabRemove() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            if (sb.charAt(0) == '\t')
                sb.delete(0, 1);

            for (int i = 1; i < sb.length() - 1; i++) {
                char c = sb.charAt(i);
                if (c == '\n' && sb.charAt(i + 1) == '\t') {
                    sb.delete(i + 1, i + 2);
                }
            }
            replaceSelection(sb);
        }
        listeners.fire(this, Event.CARET_MOVED);
    }

    private void doComment() {
        String s = pane.getSelectedText();
        if (s != null && s.length() > 0) {
            StringBuilder sb = new StringBuilder(s);
            int i = 0;
            while (i < sb.length() - 1) {
                if (sb.charAt(i) == '/' && sb.charAt(i + 1) == '/') {
                    sb.delete(i, i + 2);
                } else {
                    sb.insert(i, "//");
                    i += 2;
                }
                while (i < sb.length() - 1) {
                    if (sb.charAt(i) == '\n') {
                        i++;
                        break;
                    }
                    i++;
                }
            }
            replaceSelection(sb);
        } else {
            try {
                pane.getDocument().insertString(pane.getCaretPosition(), "/", null);
            } catch (BadLocationException e1) {
                throw new RuntimeException(e1);
            }
        }
        listeners.fire(this, Event.CARET_MOVED);
    }

    private void doNav() {
        try {
            String text = pane.getText();
            int[] sel = getCurrentWordSelection(text);
            Pos pos = Pos.toPos(text, sel[0], sel[1]);
            if (pos == null)
                return;

            String currentWord = getCurrentWord();
            if (currentWord == null)
                return;

            CompModule module = getModule();
            if (module == null)
                return;

            Expr expr = module.find(pos);
            if (expr != null) {
                Clause clause = expr.referenced();
                if (clause != null) {
                    Pos where = clause.pos();
                    if (where.sameFile(module.pos()))
                        select(where);
                    else {
                        OurSyntaxWidget ow = parent.open(where);
                        if (ow != null) {
                            ow.select(where);
                        }
                    }
                }
            }
        } catch (Exception e) {
            // Ignore, this is a best effort thingy
        }
    }

    CompModule getModule() {
        try {
            A4Reporter reporter = new A4Reporter();
            CompModule module = this.module;
            if (module == null)
                module = CompUtil.parseEverything_fromString(reporter, pane.getText());
            this.module = module;
            return module;
        } catch (Err e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    private void replaceSelection(CharSequence sb) {
        int selectionStart = pane.getSelectionStart();
        pane.replaceSelection(sb.toString());
        pane.setSelectionStart(selectionStart);
        pane.setSelectionEnd(selectionStart + sb.length());
    }

    /** Add this object into the given container. */
    public void addTo(JComponent newParent, Object constraint) {
        newParent.add(component, constraint);
    }

    /** Returns true if this textbox is currently shaded. */
    boolean shaded() {
        return pane.getHighlighter().getHighlights().length > 0;
    }

    /** Remove all shading. */
    void clearShade() {
        pane.getHighlighter().removeAllHighlights();
    }

    /**
     * Shade the range of text from start (inclusive) to end (exclusive).
     */
    void shade(Color color, int start, int end) {
        int c = color.getRGB() & 0xFFFFFF;
        if (painter == null || (painter.color.getRGB() & 0xFFFFFF) != c)
            painter = new OurHighlighter(color);
        try {
            pane.getHighlighter().addHighlight(start, end, painter);
        } catch (Throwable ex) {
        } // exception is okay
    }

    /** Returns the filename. */
    public String getFilename() {
        return filename;
    }

    /** Returns the modified-or-not flag. */
    public boolean modified() {
        return modified;
    }

    /**
     * Returns whether this textarea is based on an actual disk file.
     */
    public boolean isFile() {
        return isFile;
    }

    /**
     * Changes the font name, font size, and tab size for the document.
     */
    void setFont(String fontName, int fontSize, int tabSize) {
        if (doc != null)
            doc.do_setFont(fontName, fontSize, tabSize);
    }

    /** Enables or disables syntax highlighting. */
    void enableSyntax(boolean flag) {
        if (doc != null)
            doc.do_enableSyntax(flag);
    }

    /**
     * Return the number of lines represented by the current text (where partial
     * line counts as a line).
     * <p>
     * For example: count("")==1, count("x")==1, count("x\n")==2, and
     * count("x\ny")==2
     */
    public int getLineCount() {
        return doc.do_getLineCount();
    }

    /**
     * Return the starting offset of the given line (If "line" argument is too
     * large, it will return the last line's starting offset)
     * <p>
     * For example: given "ab\ncd\n", start(0)==0, start(1)==3, start(2...)==6. Same
     * thing when given "ab\ncd\ne".
     */
    public int getLineStartOffset(int line) {
        return doc.do_getLineStartOffset(line);
    }

    /**
     * Return the line number that the offset is in (If "offset" argument is too
     * large, it will just return do_getLineCount()-1).
     * <p>
     * For example: given "ab\ncd\n", offset(0..2)==0, offset(3..5)==1,
     * offset(6..)==2. Same thing when given "ab\ncd\ne".
     */
    public int getLineOfOffset(int offset) {
        return doc.do_getLineOfOffset(offset);
    }

    /** Returns true if we can perform undo right now. */
    public boolean canUndo() {
        return doc.do_canUndo();
    }

    /** Returns true if we can perform redo right now. */
    public boolean canRedo() {
        return doc.do_canRedo();
    }

    /** Perform undo if possible. */
    public void undo() {
        int i = doc.do_undo();
        if (i >= 0 && i <= pane.getText().length())
            moveCaret(i, i);
    }

    /** Perform redo if possible. */
    public void redo() {
        int i = doc.do_redo();
        if (i >= 0 && i <= pane.getText().length())
            moveCaret(i, i);
    }

    /** Clear the undo history. */
    public void clearUndo() {
        doc.do_clearUndo();
    }

    /** Return the caret position. */
    public int getCaret() {
        return pane.getCaretPosition();
    }

    /**
     * Select the content between offset a and offset b, and move the caret to
     * offset b.
     */
    public void moveCaret(int a, int b) {
        try {
            pane.setCaretPosition(a);
            pane.moveCaretPosition(b);
        } catch (Exception ex) {
            if (a != 0 || b != 0)
                moveCaret(0, 0);
        }
    }

    /** Return the entire text. */
    public String getText() {
        return pane.getText();
    }

    /**
     * Change the entire text to the given text (and sets the modified flag)
     */
    public void setText(String text) {
        pane.setText(text);
    }

    /** Copy the current selection into the clipboard. */
    public void copy() {
        pane.copy();
    }

    /** Cut the current selection into the clipboard. */
    public void cut() {
        pane.cut();
    }

    /** Paste the current clipboard content. */
    public void paste() {
        pane.paste();
    }

    /**
     * Discard all; if askUser is true, we'll ask the user whether to save it or not
     * if the modified==true.
     *
     * @return true if this text buffer is now a fresh empty text buffer
     */
    boolean discard(boolean askUser, Collection<String> bannedNames) {
        char ans = (!modified || !askUser) ? 'd' : OurDialog.askSaveDiscardCancel(parent.getParent(), "The file \"" + filename + "\"");
        if (ans == 'c' || (ans == 's' && save(false, bannedNames) == false))
            return false;
        for (int i = 1;; i++)
            if (!bannedNames.contains(filename = Util.canon("Untitled " + i + ".als")))
                break;
        fileModifiedDate = -1;
        pane.setText("");
        clearUndo();
        modified = false;
        isFile = false;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Discard current content then read the given file; return true if the entire
     * operation succeeds.
     */
    boolean load(String filename) {
        String x;
        try {
            x = Util.readAll(filename);
            fileModifiedDate = Util.getModifiedDate(filename);
        } catch (Throwable ex) {
            OurDialog.alert(parent.getParent(), "Error reading the file \"" + filename + "\"");
            return false;
        }
        pane.setText(x);
        moveCaret(0, 0);
        clearUndo();
        modified = false;
        isFile = true;
        this.filename = filename;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Discard (after confirming with the user) current content then reread from
     * disk file.
     */
    void reload() {
        if (!isFile)
            return; // "untitled" text buffer does not have a on-disk file to
                   // refresh from
        if (modified && !OurDialog.yesno(parent.getParent(), "You have unsaved changes to \"" + filename + "\"\nAre you sure you wish to discard " + "your changes and reload it from disk?", "Discard your changes", "Cancel this operation"))
            return;
        String t;
        try {
            t = Util.readAll(filename);
            fileModifiedDate = Util.getModifiedDate(filename);
        } catch (Throwable ex) {
            OurDialog.alert(parent.getParent(), "Cannot read \"" + filename + "\"");
            return;
        }
        if (modified == false && t.equals(pane.getText()))
            return; // no text change nor status change
        int c = pane.getCaretPosition();
        pane.setText(t);
        moveCaret(c, c);
        modified = false;
        listeners.fire(this, Event.STATUS_CHANGE);
    }

    /**
     * Save the current tab content to the file system, and return true if
     * successful.
     */
    boolean saveAs(String filename, Collection<String> bannedNames) {
        filename = Util.canon(filename);
        if (bannedNames.contains(filename)) {
            OurDialog.alert(parent.getParent(), "The filename \"" + filename + "\"\nis already open in another tab.");
            return false;
        }
        try {
            Util.writeAll(filename, pane.getText());
        } catch (Throwable e) {
            OurDialog.alert(parent.getParent(), "Error writing to the file \"" + filename + "\"");
            return false;
        }
        this.filename = Util.canon(filename); // a new file's canonical name may
                                             // change
        fileModifiedDate = Util.getModifiedDate(this.filename);
        if (fileModifiedDate == 0)
            fileModifiedDate = new Date().getTime();

        modified = false;
        isFile = true;
        listeners.fire(this, Event.STATUS_CHANGE);
        return true;
    }

    /**
     * Save the current tab content to the file system and return true if
     * successful.
     *
     * @param alwaysPickNewName - if true, it will always pop up a File Selection
     *            dialog box to ask for the filename
     */
    boolean save(boolean alwaysPickNewName, Collection<String> bannedNames) {
        String n = this.filename;
        if (alwaysPickNewName || isFile == false || n.startsWith(Util.jarPrefix())) {
            File f = OurDialog.askFile(new Frame("Alloy File Dialog"), false, null, ".als", ".als files");
            if (f == null)
                return false;
            n = Util.canon(f.getPath());
            if (f.exists() && !OurDialog.askOverwrite(parent.getParent(), n))
                return false;
        }

        if (isFile && n.equals(this.filename) && Util.getModifiedDate(this.filename) > fileModifiedDate) {
            if (!OurDialog.yesno(parent.getParent(), "The file has been modified outside the editor.\n" + "Do you want to overwrite it anyway?")) {
                return false;
            }
        }

        if (saveAs(n, bannedNames)) {
            Util.setCurrentDirectory(new File(filename).getParentFile());
            return true;
        } else
            return false;
    }

    /** Transfer focus to this component. */
    public void requestFocusInWindow() {
        if (pane != null)
            pane.requestFocusInWindow();
    }

    public void select(Pos pos) {
        String doc = pane.getText();
        int[] selection = pos.toStartEnd(doc);
        if (selection == null)
            return;

        pane.setSelectionStart(selection[0]);
        pane.setSelectionEnd(selection[1]);
    }

    public String getTooltip(MouseEvent event) {
        try {
            int offset = pane.viewToModel(event.getPoint());
            CompModule module = getModule();
            if (module == null)
                return null;

            String text = pane.getText();
            Pos pos = Pos.toPos(text, offset, offset + 1);
            Expr expr = module.find(pos);
            if (expr instanceof ExprBad) {
                return expr.toString();
            }
            if (expr != null) {
                Clause referenced = expr.referenced();
                if (referenced != null) {
                    String s = referenced.explain();
                    String table = "<html><pre>" + s + "</pre></html>";
                    s = table.replaceAll("\n", "<br/>");
                    return s;
                } else if (expr instanceof ExprConstant) {
                    String token = pos.substring(text);
                    if (token != null) {
                        String match = expr.toString();
                        if (!Objects.equals(token, match))
                            return match;
                    }
                }
            }
        } catch (Exception e) {
            // e.printStackTrace();
            // ignore compile errors etc.
        }
        return null;
    }
}
