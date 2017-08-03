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
import java.awt.event.ActionEvent;
import java.awt.event.FocusAdapter;
import java.awt.event.FocusEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.io.File;
import java.util.Collection;
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
import javax.swing.text.BoxView;
import javax.swing.text.Document;
import javax.swing.text.Element;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.View;
import javax.swing.text.ViewFactory;
import edu.mit.csail.sdg.alloy4.Listener.Event;

/** Graphical syntax-highlighting editor.
 *
 * <p><b>Thread Safety:</b> Can be called only by the AWT event thread
 */

public final class OurSyntaxWidget {

   /** The current list of listeners; possible events are { STATUS_CHANGE, FOCUSED, CTRL_PAGE_UP, CTRL_PAGE_DOWN, CARET_MOVED }. */
   public final Listeners listeners = new Listeners();

   /** The JScrollPane containing everything. */
   private final JScrollPane component = OurUtil.make(new JScrollPane(), new EmptyBorder(0, 0, 0, 0));

   /** This is an optional JComponent annotation. */
   public final JComponent obj1;

   /** This is an optional JComponent annotation. */
   public final JComponent obj2;

   /** The underlying StyledDocument being displayed (changes will trigger the STATUS_CHANGE event) */
   private final OurSyntaxUndoableDocument doc = new OurSyntaxUndoableDocument("Monospaced", 14);

   /** The underlying JTextPane being displayed. */
   private final JTextPane pane = OurAntiAlias.pane(Color.BLACK, Color.WHITE, new EmptyBorder(1, 1, 1, 1));

   /** The filename for this JTextPane (changes will trigger the STATUS_CHANGE event) */
   private String filename = "";

   /** Whether this JTextPane has been modified since last load/save (changes will trigger the STATUS_CHANGE event) */
   private boolean modified;

   /** Whether this JTextPane corresponds to an existing disk file (changes will trigger the STATUS_CHANGE event) */
   private boolean isFile;

   /** Caches the most recent background painter if nonnull. */
   private OurHighlighter painter;

   /** Constructs a syntax-highlighting widget. */
   public OurSyntaxWidget() { this(true, "", "Monospaced", 14, 4, null, null); }

   /** Constructs a syntax-highlighting widget. */
   @SuppressWarnings("serial")
   public OurSyntaxWidget
   (boolean enableSyntax, String text, String fontName, int fontSize, int tabSize, JComponent obj1, JComponent obj2) {
      this.obj1 = obj1;
      this.obj2 = obj2;
      final OurSyntaxWidget me = this;
      final ViewFactory defaultFactory = (new StyledEditorKit()).getViewFactory();
      doc.do_enableSyntax(enableSyntax);
      doc.do_setFont(fontName, fontSize, tabSize);
      pane.setEditorKit(new StyledEditorKit() { // Prevents line-wrapping up to width=30000, and tells it to use our Document obj
         @Override public Document createDefaultDocument() { return doc; }
         @Override public ViewFactory getViewFactory() {
            return new ViewFactory() {
               public View create(Element x) {
                  if (!AbstractDocument.SectionElementName.equals(x.getName())) return defaultFactory.create(x);
                  return new BoxView(x, View.Y_AXIS) { // 30000 is a good width to use here; value > 32767 appears to cause errors
                     @Override public final float getMinimumSpan(int axis) { return super.getPreferredSpan(axis); }
                     @Override public final void layout(int w, int h) { try {super.layout(30000, h);} catch(Throwable ex) {} }
                  };
               }
            };
         }
      });
      if (text.length()>0) { pane.setText(text); pane.setCaretPosition(0); }
      doc.do_clearUndo();
      pane.getActionMap().put("alloy_copy", new AbstractAction("alloy_copy") {
         public void actionPerformed(ActionEvent e) { pane.copy(); }
      });
      pane.getActionMap().put("alloy_cut", new AbstractAction("alloy_cut") {
         public void actionPerformed(ActionEvent e) { pane.cut(); }
      });
      pane.getActionMap().put("alloy_paste", new AbstractAction("alloy_paste") {
         public void actionPerformed(ActionEvent e) { pane.paste(); }
      });
      pane.getActionMap().put("alloy_ctrl_pageup", new AbstractAction("alloy_ctrl_pageup") {
         public void actionPerformed(ActionEvent e) { listeners.fire(me, Event.CTRL_PAGE_UP); }
      });
      pane.getActionMap().put("alloy_ctrl_pagedown", new AbstractAction("alloy_ctrl_pagedown") {
         public void actionPerformed(ActionEvent e) { listeners.fire(me, Event.CTRL_PAGE_DOWN); }
      });
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.CTRL_MASK), "alloy_copy");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_X, InputEvent.CTRL_MASK), "alloy_cut");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_V, InputEvent.CTRL_MASK), "alloy_paste");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.CTRL_MASK), "alloy_copy");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_INSERT, InputEvent.SHIFT_MASK), "alloy_paste");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_DELETE, InputEvent.SHIFT_MASK), "alloy_cut");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_UP, InputEvent.CTRL_MASK), "alloy_ctrl_pageup");
      pane.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_PAGE_DOWN, InputEvent.CTRL_MASK), "alloy_ctrl_pagedown");
      doc.addDocumentListener(new DocumentListener() {
         public void insertUpdate(DocumentEvent e) { modified=true; listeners.fire(me, Event.STATUS_CHANGE); }
         public void removeUpdate(DocumentEvent e) { modified=true; listeners.fire(me, Event.STATUS_CHANGE); }
         public void changedUpdate(DocumentEvent e) { }
      });
      pane.addFocusListener(new FocusAdapter() {
         @Override public void focusGained(FocusEvent e) { listeners.fire(me, Event.FOCUSED); }
      });
      pane.addCaretListener(new CaretListener() {
         public void caretUpdate(CaretEvent e) { listeners.fire(me, Event.CARET_MOVED); }
      });
      component.addFocusListener(new FocusAdapter() {
         @Override public void focusGained(FocusEvent e) { pane.requestFocusInWindow(); }
      });
      component.setFocusable(false);
      component.setMinimumSize(new Dimension(50, 50));
      component.setViewportView(pane);
      modified = false;
   }

   /** Add this object into the given container. */
   public void addTo(JComponent newParent, Object constraint) { newParent.add(component, constraint); }

   /** Returns true if this textbox is currently shaded. */
   boolean shaded() { return pane.getHighlighter().getHighlights().length > 0; }

   /** Remove all shading. */
   void clearShade() { pane.getHighlighter().removeAllHighlights(); }

   /** Shade the range of text from start (inclusive) to end (exclusive). */
   void shade(Color color, int start, int end) {
      int c = color.getRGB() & 0xFFFFFF;
      if (painter==null || (painter.color.getRGB() & 0xFFFFFF)!=c)  painter = new OurHighlighter(color);
      try { pane.getHighlighter().addHighlight(start, end, painter); } catch(Throwable ex) { } // exception is okay
   }

   /** Returns the filename. */
   public String getFilename() { return filename; }

   /** Returns the modified-or-not flag. */
   public boolean modified() { return modified; }

   /** Returns whether this textarea is based on an actual disk file. */
   public boolean isFile() { return isFile; }

   /** Changes the font name, font size, and tab size for the document. */
   void setFont(String fontName, int fontSize, int tabSize) { if (doc!=null) doc.do_setFont(fontName, fontSize, tabSize); }

   /** Enables or disables syntax highlighting. */
   void enableSyntax(boolean flag) { if (doc!=null) doc.do_enableSyntax(flag); }

   /** Return the number of lines represented by the current text (where partial line counts as a line).
    * <p> For example: count("")==1, count("x")==1, count("x\n")==2, and count("x\ny")==2
    */
   public int getLineCount()  { return doc.do_getLineCount();  }

   /** Return the starting offset of the given line (If "line" argument is too large, it will return the last line's starting offset)
    * <p> For example: given "ab\ncd\n", start(0)==0, start(1)==3, start(2...)==6.  Same thing when given "ab\ncd\ne".
    */
   public int getLineStartOffset(int line) { return doc.do_getLineStartOffset(line); }

   /** Return the line number that the offset is in (If "offset" argument is too large, it will just return do_getLineCount()-1).
    * <p> For example: given "ab\ncd\n", offset(0..2)==0, offset(3..5)==1, offset(6..)==2.  Same thing when given "ab\ncd\ne".
    */
   public int getLineOfOffset(int offset) { return doc.do_getLineOfOffset(offset); }

   /** Returns true if we can perform undo right now. */
   public boolean canUndo() { return doc.do_canUndo(); }

   /** Returns true if we can perform redo right now. */
   public boolean canRedo() { return doc.do_canRedo(); }

   /** Perform undo if possible. */
   public void undo() { int i = doc.do_undo(); if (i>=0 && i<=pane.getText().length()) moveCaret(i, i); }

   /** Perform redo if possible. */
   public void redo() { int i = doc.do_redo(); if (i>=0 && i<=pane.getText().length()) moveCaret(i, i); }

   /** Clear the undo history. */
   public void clearUndo() { doc.do_clearUndo(); }

   /** Return the caret position. */
   public int getCaret() { return pane.getCaretPosition(); }

   /** Select the content between offset a and offset b, and move the caret to offset b. */
   public void moveCaret(int a, int b) {
      try { pane.setCaretPosition(a); pane.moveCaretPosition(b); } catch(Exception ex) { if (a!=0 || b!=0) moveCaret(0, 0); }
   }

   /** Return the entire text. */
   public String getText() { return pane.getText(); }

   /** Change the entire text to the given text (and sets the modified flag) */
   public void setText(String text) { pane.setText(text); }

   /** Copy the current selection into the clipboard. */
   public void copy() { pane.copy(); }

   /** Cut the current selection into the clipboard. */
   public void cut() { pane.cut(); }

   /** Paste the current clipboard content. */
   public void paste() { pane.paste(); }

   /** Discard all; if askUser is true, we'll ask the user whether to save it or not if the modified==true.
    * @return true if this text buffer is now a fresh empty text buffer
    */
   boolean discard(boolean askUser, Collection<String> bannedNames) {
      char ans = (!modified || !askUser) ? 'd' : OurDialog.askSaveDiscardCancel("The file \"" + filename + "\"");
      if (ans=='c' || (ans=='s' && save(false, bannedNames)==false)) return false;
      for(int i=1; ;i++) if (!bannedNames.contains(filename = Util.canon("Untitled " + i + ".als"))) break;
      pane.setText(""); clearUndo(); modified=false; isFile=false; listeners.fire(this, Event.STATUS_CHANGE);
      return true;
   }

   /** Discard current content then read the given file; return true if the entire operation succeeds. */
   boolean load(String filename) {
      String x;
      try {
         x = Util.readAll(filename);
      } catch(Throwable ex) { OurDialog.alert("Error reading the file \"" + filename + "\""); return false; }
      pane.setText(x); moveCaret(0,0); clearUndo(); modified=false; isFile=true; this.filename=filename;
      listeners.fire(this, Event.STATUS_CHANGE);
      return true;
   }

   /** Discard (after confirming with the user) current content then reread from disk file. */
   void reload() {
      if (!isFile) return; // "untitled" text buffer does not have a on-disk file to refresh from
      if (modified && !OurDialog.yesno("You have unsaved changes to \"" + filename + "\"\nAre you sure you wish to discard "
            + "your changes and reload it from disk?", "Discard your changes", "Cancel this operation")) return;
      String t;
      try { t=Util.readAll(filename); } catch(Throwable ex) { OurDialog.alert("Cannot read \""+filename+"\""); return; }
      if (modified==false && t.equals(pane.getText())) return; // no text change nor status change
      int c=pane.getCaretPosition();  pane.setText(t);  moveCaret(c,c);  modified=false;  listeners.fire(this, Event.STATUS_CHANGE);
   }

   /** Save the current tab content to the file system, and return true if successful. */
   boolean saveAs(String filename, Collection<String> bannedNames) {
      filename = Util.canon(filename);
      if (bannedNames.contains(filename)) {
         OurDialog.alert("The filename \""+filename+"\"\nis already open in another tab.");
         return false;
      }
      try { Util.writeAll(filename, pane.getText()); }
      catch (Throwable e) { OurDialog.alert("Error writing to the file \""+filename+"\""); return false; }
      this.filename = Util.canon(filename); // a new file's canonical name may change
      modified=false; isFile=true; listeners.fire(this, Event.STATUS_CHANGE);  return true;
   }

   /** Save the current tab content to the file system and return true if successful.
    * @param alwaysPickNewName - if true, it will always pop up a File Selection dialog box to ask for the filename
    */
   boolean save(boolean alwaysPickNewName, Collection<String> bannedNames) {
      String n = this.filename;
      if (alwaysPickNewName || isFile==false || n.startsWith(Util.jarPrefix())) {
         File f = OurDialog.askFile(false, null, ".als", ".als files");  if (f==null) return false;
         n = Util.canon(f.getPath());   if (f.exists() && !OurDialog.askOverwrite(n)) return false;
      }
      if (saveAs(n, bannedNames)) {Util.setCurrentDirectory(new File(filename).getParentFile()); return true;} else return false;
   }

   /** Transfer focus to this component. */
   public void requestFocusInWindow() { if (pane!=null) pane.requestFocusInWindow(); }
}
