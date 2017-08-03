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
import java.awt.Font;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.List;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultEditorKit;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.TabSet;
import javax.swing.text.TabStop;
import static edu.mit.csail.sdg.alloy4.OurConsole.style;

/** Graphical syntax-highlighting StyledDocument.
 *
 * <p><b>Thread Safety:</b> Can be called only by the AWT event thread
 */

class OurSyntaxDocument extends DefaultStyledDocument {

   /** This ensures the class can be serialized reliably. */
   private static final long serialVersionUID = 0;

   /** The "comment mode" at the start of each line (0 = no comment) (1 = block comment) (2 = javadoc comment) (-1 = unknown) */
   private final List<Integer> comments = new ArrayList<Integer>();

   /** Whether syntax highlighting is currently enabled or not. */
   private boolean enabled = true;

   /** The current font name is. */
   private String font = "Monospaced";

   /** The current font size. */
   private int fontSize = 14;

   /** The current tab size. */
   private int tabSize = 4;

   /** The list of font+color styles (eg. regular text, symbols, keywords, comments, etc). */
   private final List<MutableAttributeSet> all = new ArrayList<MutableAttributeSet>();

   /** The character style for regular text. */
   private final MutableAttributeSet styleNormal  = style(font, fontSize, false, Color.BLACK, 0);          { all.add(styleNormal); }

   /** The character style for symbols. */
   private final MutableAttributeSet styleSymbol  = style(font, fontSize, true, Color.BLACK, 0);           { all.add(styleSymbol); }

   /** The character style for integer constants. */
   private final MutableAttributeSet styleNumber  = style(font, fontSize, true, new Color(0xA80A0A), 0);   { all.add(styleNumber); }

   /** The character style for keywords. */
   private final MutableAttributeSet styleKeyword = style(font, fontSize, true, new Color(0x1E1EA8), 0);   { all.add(styleKeyword); }

   /** The character style for string literals. */
   private final MutableAttributeSet styleString  = style(font, fontSize, false, new Color(0xA80AA8), 0);  { all.add(styleString); }

   /** The character style for up-to-end-of-line-style comment. */
   private final MutableAttributeSet styleComment = style(font, fontSize, false, new Color(0x0A940A), 0);  { all.add(styleComment); }

   /** The character style for non-javadoc-style block comment. */
   private final MutableAttributeSet styleBlock   = style(font, fontSize, false, new Color(0x0A940A), 0);  { all.add(styleBlock); }

   /** The character style for javadoc-style block comment. */
   private final MutableAttributeSet styleJavadoc = style(font, fontSize, true, new Color(0x0A940A), 0);   { all.add(styleJavadoc); }

   /** The paragraph style for indentation. */
   private final MutableAttributeSet tabset = new SimpleAttributeSet();

   /** This stores the currently recognized set of reserved keywords. */
   private static final String[] keywords = new String[] {"abstract", "all", "and", "as", "assert", "but", "check", "disj",
      "disjoint", "else", "enum", "exactly", "exh", "exhaustive", "expect", "extends", "fact", "for", "fun", "iden",
      "iff", "implies", "in", "Int", "int", "let", "lone", "module", "no", "none", "not", "one", "open", "or", "part",
      "partition", "pred", "private", "run", "seq", "set", "sig", "some", "String", "sum", "this", "univ"
   };

   /** Returns true if array[start .. start+len-1] matches one of the reserved keyword. */
   private static final boolean do_keyword(String array, int start, int len) {
      if (len >= 2 && len <= 10) for(int i = keywords.length - 1; i >= 0; i--) {
         String str = keywords[i];
         if (str.length()==len) for(int j=0; ;j++) if (j==len) return true; else if (str.charAt(j) != array.charAt(start+j)) break;
      }
      return false;
   }

   /** Returns true if "c" can be in the start or middle or end of an identifier. */
   private static final boolean do_iden(char c) {
      return (c>='A' && c<='Z') || (c>='a' && c<='z') || c=='$' || (c>='0' && c<='9') || c=='_' || c=='\'' || c=='\"';
   }

   /** Constructor. */
   public OurSyntaxDocument(String fontName, int fontSize) {
      putProperty(DefaultEditorKit.EndOfLineStringProperty, "\n");
      tabSize++;
      do_setFont(fontName, fontSize, tabSize - 1); // assigns the given font, and also forces recomputation of the tab size
   }

   /** Enables or disables syntax highlighting. */
   public final void do_enableSyntax (boolean flag) {
      if (enabled == flag) return; else { enabled = flag;  comments.clear(); }
      if (flag) do_reapplyAll(); else setCharacterAttributes(0, getLength(), styleNormal, false);
   }

   /** Return the number of lines represented by the current text (where partial line counts as a line).
    * <p> For example: count("")==1, count("x")==1, count("x\n")==2, and count("x\ny")==2
    */
   public final int do_getLineCount() {
      String txt = toString();
      for(int n=txt.length(), ans=1, i=0; ; i++) if (i>=n) return ans; else if (txt.charAt(i)=='\n') ans++;
   }

   /** Return the starting offset of the given line (If "line" argument is too large, it will return the last line's starting offset)
    * <p> For example: given "ab\ncd\n", start(0)==0, start(1)==3, start(2...)==6.  Same thing when given "ab\ncd\ne".
    */
   public final int do_getLineStartOffset(int line) {
      String txt = toString();
      for(int n=txt.length(), ans=0, i=0, y=0; ; i++) if (i>=n || y>=line) return ans; else if (txt.charAt(i)=='\n') {ans=i+1; y++;}
   }

   /** Return the line number that the offset is in (If "offset" argument is too large, it will just return do_getLineCount()-1).
    * <p> For example: given "ab\ncd\n", offset(0..2)==0, offset(3..5)==1, offset(6..)==2.  Same thing when given "ab\ncd\ne".
    */
   public final int do_getLineOfOffset(int offset) {
      String txt = toString();
      for(int n=txt.length(), ans=0, i=0; ; i++) if (i>=n || i>=offset) return ans; else if (txt.charAt(i)=='\n') ans++;
   }

   /** This method is called by Swing to insert a String into this document.
    * We intentionally ignore "attr" and instead use our own coloring.
    */
   @Override public void insertString(int offset, String string, AttributeSet attr) throws BadLocationException {
      if (string.indexOf('\r')>=0) string = Util.convertLineBreak(string); // we don't want '\r'
      if (!enabled) { super.insertString(offset, string, styleNormal); return; }
      int startLine = do_getLineOfOffset(offset);
      for(int i = 0; i < string.length(); i++) { // For each inserted '\n' we need to shift the values in "comments" array down
         if (string.charAt(i)=='\n') { if (startLine < comments.size()-1) comments.add(startLine+1, -1); }
      }
      super.insertString(offset, string, styleNormal);
      try { do_update(startLine); } catch(Exception ex) { comments.clear(); }
   }

   /** This method is called by Swing to delete text from this document. */
   @Override public void remove(int offset, int length) throws BadLocationException {
      if (!enabled) { super.remove(offset, length); return; }
      int i = 0, startLine = do_getLineOfOffset(offset);
      for(String oldText = toString(); i<length; i++) { // For each deleted '\n' we need to shift the values in "comments" array up
         if (oldText.charAt(offset+i)=='\n') if (startLine < comments.size()-1) comments.remove(startLine+1);
      }
      super.remove(offset, length);
      try { do_update(startLine); } catch(Exception ex) { comments.clear(); }
   }

   /** This method is called by Swing to replace text in this document. */
   @Override public void replace(int offset, int length, String string, AttributeSet attrs) throws BadLocationException {
      if (length > 0) this.remove(offset, length);
      if (string != null && string.length() > 0) this.insertString(offset, string, styleNormal);
   }

   /** Reapply styles assuming the given line has just been modified */
   private final void do_update(int line) throws BadLocationException  {
      String content = toString();
      int lineCount = do_getLineCount();
      while(line>0 && (line>=comments.size() || comments.get(line)<0)) line--; // "-1" in comments array are always contiguous
      int comment = do_reapply(line==0 ? 0 : comments.get(line), content, line);
      for (line++; line < lineCount; line++) { // update each subsequent line until it already starts with its expected comment mode
         if (line < comments.size() && comments.get(line) == comment) break; else comment = do_reapply(comment, content, line);
      }
   }

   /** Re-color the given line assuming it starts with a given comment mode, then return the comment mode for start of next line. */
   private final int do_reapply(int comment, final String txt, final int line) {
      while (line >= comments.size()) comments.add(-1); // enlarge array if needed
      comments.set(line, comment);                      // record the fact that this line starts with the given comment mode
      for(int n = txt.length(), i = do_getLineStartOffset(line); i < n;) {
         final int oldi = i;
         final char c = txt.charAt(i);
         if (c=='\n') break;
         if (comment==0 && c=='/' && i<n-3 && txt.charAt(i+1)=='*' && txt.charAt(i+2)=='*' && txt.charAt(i+3)!='/') comment = 2;
         if (comment==0 && c=='/' && i==n-3 && txt.charAt(i+1)=='*' && txt.charAt(i+2)=='*') comment = 2;
         if (comment==0 && c=='/' && i<n-1 && txt.charAt(i+1)=='*') { comment = 1; i = i + 2; }
         if (comment>0) {
            AttributeSet style = (comment==1 ? styleBlock : styleJavadoc);
            while(i<n && txt.charAt(i)!='\n' && (txt.charAt(i)!='*' || i+1==n || txt.charAt(i+1)!='/')) i = i + 1;
            if (i<n-1 && txt.charAt(i)=='*' && txt.charAt(i+1)=='/') { i = i + 2; comment = 0; }
            setCharacterAttributes(oldi, i-oldi, style, false);
         } else if ((c=='/' || c=='-') && i<n-1 && txt.charAt(i+1)==c) {
            i = txt.indexOf('\n', i);
            setCharacterAttributes(oldi, i<0 ? (n-oldi) : (i-oldi), styleComment, false);
            break;
         } else if (c=='\"') {
            for(i++; i<n; i++) {
               if (txt.charAt(i)=='\n') break;
               if (txt.charAt(i)=='\"') {i++; break;}
               if (txt.charAt(i)=='\\' && i+1<n && txt.charAt(i+1)!='\n') i++;
            }
            setCharacterAttributes(oldi, i-oldi, styleString, false);
         } else if (do_iden(c)) {
            for(i++; i<n && do_iden(txt.charAt(i)); i++) { }
            AttributeSet style = (c>='0' && c<='9') ? styleNumber : (do_keyword(txt, oldi, i-oldi) ? styleKeyword : styleNormal);
            setCharacterAttributes(oldi, i-oldi, style, false);
         } else {
            for(i++; i<n && !do_iden(txt.charAt(i)) && txt.charAt(i)!='\n' && txt.charAt(i)!='-' && txt.charAt(i)!='/'; i++) { }
            setCharacterAttributes(oldi, i-oldi, styleSymbol, false);
         }
      }
      return comment;
   }

   /** Reapply the appropriate style to the entire document. */
   private final void do_reapplyAll() {
      setCharacterAttributes(0, getLength(), styleNormal, true);
      comments.clear();
      String content = toString();
      for(int comment = 0, i = 0, n = do_getLineCount(); i < n; i++)  comment = do_reapply(comment, content, i);
   }

   /** Changes the font and tabsize for the document. */
   public final void do_setFont(String fontName, int fontSize, int tabSize) {
      if (tabSize < 1) tabSize = 1; else if (tabSize > 100) tabSize = 100;
      if (fontName.equals(this.font) && fontSize == this.fontSize && tabSize == this.tabSize) return;
      this.font = fontName;
      this.fontSize = fontSize;
      this.tabSize = tabSize;
      for(MutableAttributeSet s: all) { StyleConstants.setFontFamily(s, fontName);  StyleConstants.setFontSize(s, fontSize); }
      do_reapplyAll();
      BufferedImage im = new BufferedImage(10, 10, BufferedImage.TYPE_INT_RGB); // this is used to derive the tab width
      int gap = tabSize * im.createGraphics().getFontMetrics(new Font(fontName, Font.PLAIN, fontSize)).charWidth('X');
      TabStop[] pos = new TabStop[100];
      for(int i=0; i<100; i++) { pos[i] = new TabStop(i*gap + gap); }
      StyleConstants.setTabSet(tabset, new TabSet(pos));
      setParagraphAttributes(0, getLength(), tabset, false);
   }

   /** Overriden to return the full text of the document.
    * @return the entire text
    */
   @Override public String toString() {
      try { return getText(0, getLength()); } catch(BadLocationException ex) { return ""; }
   }
}
