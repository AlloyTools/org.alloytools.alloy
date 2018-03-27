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

import static java.lang.System.arraycopy;

import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.SimpleAttributeSet;

/**
 * Graphical syntax-highlighting StyledDocument with undo+redo support.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread
 */

final class OurSyntaxUndoableDocument extends OurSyntaxDocument {

    /** This ensures the class can be serialized reliably. */
    private static final long  serialVersionUID = 0;

    /** The maximum number of UNDO actions we want to keep. */
    private static final int   MAXUNDO          = 100;

    /**
     * For each i = 0..now-1, insert[i] means whether the i-th operation was an
     * insertion or not.
     */
    private boolean            insert[]         = new boolean[MAXUNDO];

    /**
     * For each i = 0..now-1, text[i] means the i-th operation was an
     * insertion/deletion of that text.
     */
    private String             text[]           = new String[MAXUNDO];

    /**
     * For each i = 0..now-1, where[i] means the i-th operation was an
     * insertion/deletion at that offset.
     */
    private int                where[]          = new int[MAXUNDO];

    /**
     * The number of undoable operations currently remembered in insert[], text[],
     * and where[].
     */
    private int                now;

    /**
     * The number of undoable opeartions that are currently "undone".
     */
    private int                undone;

    /**
     * Caches a default AttributeSet (just so that we don't pass null as a
     * AttributeSet.
     */
    private final AttributeSet attr             = new SimpleAttributeSet();

    /** Constructor. */
    public OurSyntaxUndoableDocument(String fontName, int fontSize) {
        super(fontName, fontSize);
    }

    /** Clear the undo history. */
    public void do_clearUndo() {
        now = undone = 0;
    }

    /** Returns true if we can perform undo right now. */
    public boolean do_canUndo() {
        return undone < now;
    }

    /** Returns true if we can perform redo right now. */
    public boolean do_canRedo() {
        return undone > 0;
    }

    /**
     * Perform undo then return where the new desired caret location should be (or
     * return -1 if undo is not possible right now)
     */
    public int do_undo() {
        if (undone >= now)
            return -1;
        else
            undone++;
        boolean insert = this.insert[now - undone];
        String text = this.text[now - undone];
        int where = this.where[now - undone];
        try {
            if (insert) {
                super.remove(where, text.length());
                return where;
            } else {
                super.insertString(where, text, attr);
                return where + text.length();
            }
        } catch (BadLocationException ex) {
            return -1;
        }
    }

    /**
     * Perform redo then return where the new desired caret location should be (or
     * return -1 if redo is not possible right now)
     */
    public int do_redo() {
        if (undone <= 0)
            return -1;
        boolean insert = this.insert[now - undone];
        String text = this.text[now - undone];
        int where = this.where[now - undone];
        undone--;
        try {
            if (insert) {
                super.insertString(where, text, attr);
                return where + text.length();
            } else {
                super.remove(where, text.length());
                return where;
            }
        } catch (BadLocationException ex) {
            return -1;
        }
    }

    /**
     * This method is called by Swing to insert a String into this document.
     */
    @Override
    public void insertString(int offset, String string, AttributeSet attr) throws BadLocationException {
        if (string.length() == 0)
            return;
        else if (string.indexOf('\r') >= 0)
            string = Util.convertLineBreak(string); // we don't want '\r'
        if (undone > 0) {
            now = now - undone;
            undone = 0;
        } // clear the REDO entries
        super.insertString(offset, string, attr);
        if (now > 0 && insert[now - 1]) { // merge with last edit if possible
            if (where[now - 1] == offset - text[now - 1].length()) {
                text[now - 1] += string;
                return;
            }
        }
        if (now >= MAXUNDO) {
            arraycopy(insert, 1, insert, 0, MAXUNDO - 1);
            arraycopy(text, 1, text, 0, MAXUNDO - 1);
            arraycopy(where, 1, where, 0, MAXUNDO - 1);
            now--;
        }
        insert[now] = true;
        text[now] = string;
        where[now] = offset;
        now++;
    }

    /**
     * This method is called by Swing to delete text from this document.
     */
    @Override
    public void remove(int offset, int length) throws BadLocationException {
        if (length == 0)
            return;
        if (undone > 0) {
            now = now - undone;
            undone = 0;
        } // clear the REDO entries
        String string = toString().substring(offset, offset + length);
        super.remove(offset, length);
        if (now > 0 && !insert[now - 1]) { // merge with last edit if possible
            if (where[now - 1] == offset) {
                text[now - 1] += string;
                return;
            }
            if (where[now - 1] == offset + length) {
                where[now - 1] = offset;
                text[now - 1] = string + text[now - 1];
                return;
            }
        }
        if (now >= MAXUNDO) {
            arraycopy(insert, 1, insert, 0, MAXUNDO - 1);
            arraycopy(text, 1, text, 0, MAXUNDO - 1);
            arraycopy(where, 1, where, 0, MAXUNDO - 1);
            now--;
        }
        insert[now] = false;
        text[now] = string;
        where[now] = offset;
        now++;
    }

    /**
     * This method is called by Swing to replace text in this document.
     */
    @Override
    public void replace(int offset, int length, String string, AttributeSet attrs) throws BadLocationException {
        if (length > 0)
            this.remove(offset, length);
        if (string != null && string.length() > 0)
            this.insertString(offset, string, this.attr);
    }

    /**
     * Overriden to return the full text of the document.
     *
     * @return the entire text
     */
    @Override
    public String toString() {
        try {
            return getText(0, getLength());
        } catch (BadLocationException ex) {
            return "";
        }
    }
}
