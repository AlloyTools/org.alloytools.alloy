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

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Font;
import java.awt.Rectangle;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.LinkedHashMap;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import edu.mit.csail.sdg.alloy4.Listener.Event;

/** Graphical multi-tabbed syntax-highlighting editor.
 *
 * <p><b>Thread Safety:</b> Can be called only by the AWT event thread.
 *
 * <p><b>Invariant</b>: each tab has distinct file name.
 */

public final class OurTabbedSyntaxWidget {

   /** The current list of listeners; possible events are { STATUS_CHANGE, FOCUSED, CARET_MOVED }. */
   public final Listeners listeners = new Listeners();

   /** The JScrollPane containing everything. */
   private final JPanel component = OurUtil.make(new JPanel());

   /** Background color for the list of tabs. */
   private static final Color GRAY = new Color(0.9f, 0.9f, 0.9f);

   /** Background color for an inactive tab. */
   private static final Color INACTIVE = new Color(0.8f, 0.8f, 0.8f);

   /** Background color for a inactive and highlighted tab. */
   private static final Color INACTIVE_HIGHLIGHTED = new Color(0.7f, 0.5f, 0.5f);

   /** Foreground color for a active and highlighted tab. */
   private static final Color ACTIVE_HIGHLIGHTED = new Color(0.5f, 0.2f, 0.2f);

   /** Default border color for each tab. */
   private static final Color BORDER = Color.LIGHT_GRAY;

   /** The font name to use in the JTextArea */
   private String fontName = "Monospaced";

   /** The font size to use in the JTextArea */
   private int fontSize = 14;

   /** The tabsize to use in the JTextArea */
   private int tabSize = 4;

   /** Whether syntax highlighting is current enabled or not. */
   private boolean syntaxHighlighting;

   /** The list of clickable tabs. */
   private final JPanel tabBar;

   /** The scrollPane that wraps around this.tabbar */
   private final JScrollPane tabBarScroller;

   /** The list of tabs. */
   private final List<OurSyntaxWidget> tabs = new ArrayList<OurSyntaxWidget>();

   /** The currently selected tab from 0 to list.size()-1 (This value must be 0 if there are no tabs) */
   private int me = 0;

   /** This object receives messages from sub-JTextPane objects. */
   private final Listener listener = new Listener() {
      public Object do_action(Object sender, Event e) {
         final OurTabbedSyntaxWidget me = OurTabbedSyntaxWidget.this;
         if (sender instanceof OurSyntaxWidget) switch(e) {
            case FOCUSED:        listeners.fire(me, e); break;
            case CARET_MOVED:    listeners.fire(me, Event.STATUS_CHANGE); break;
            case CTRL_PAGE_UP:   prev(); break;
            case CTRL_PAGE_DOWN: next(); break;
            case STATUS_CHANGE:
               clearShade();
               OurSyntaxWidget t = (OurSyntaxWidget)sender;
               String n = t.getFilename();
               t.obj1.setToolTipText(n);
               int i = n.lastIndexOf('/'); if (i >= 0) n = n.substring(i + 1);
               i = n.lastIndexOf('\\');    if (i >= 0) n = n.substring(i + 1);
               i = n.lastIndexOf('.');     if (i >= 0) n = n.substring(0, i);
               if (n.length() > 14) { n = n.substring(0, 14) + "..."; }
               if (t.obj1 instanceof JLabel) { ((JLabel)(t.obj1)).setText("  " + n + (t.modified() ? " *  " : "  ")); }
               listeners.fire(me, Event.STATUS_CHANGE);
               break;
         }
         return true;
      }
      public Object do_action(Object sender, Event e, Object arg) { return true;  }
   };

   /** Constructs a tabbed editor pane. */
   public OurTabbedSyntaxWidget(String fontName, int fontSize, int tabSize) {
      component.setBorder(null);
      component.setLayout(new BorderLayout());
      JPanel glue = OurUtil.makeHB(new Object[]{null});
      glue.setBorder(new OurBorder(null, null, BORDER, null));
      tabBar = OurUtil.makeHB(glue);
      if (!Util.onMac()) { tabBar.setOpaque(true); tabBar.setBackground(GRAY); }
      tabBarScroller = new JScrollPane(tabBar, JScrollPane.VERTICAL_SCROLLBAR_NEVER, JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
      tabBarScroller.setFocusable(false);
      tabBarScroller.setBorder(null);
      setFont(fontName, fontSize, tabSize);
      newtab(null);
      tabBarScroller.addComponentListener(new ComponentListener() {
         public final void componentResized(ComponentEvent e) { select(me); }
         public final void componentMoved(ComponentEvent e) { select(me); }
         public final void componentShown(ComponentEvent e) { select(me); }
         public final void componentHidden(ComponentEvent e) { }
      });
   }

   /** Add this object into the given container. */
   public void addTo(JComponent newParent, Object constraint) { newParent.add(component, constraint); }

   /** Adjusts the background and foreground of all labels. */
   private void adjustLabelColor() {
      for(int i=0; i<tabs.size(); i++) {
         OurSyntaxWidget tab = tabs.get(i);
         boolean hl = tab.shaded();
         tab.obj1.setBorder(new OurBorder(BORDER, BORDER, (i!=me ? BORDER : Color.WHITE), BORDER));
         tab.obj1.setBackground(i!=me ? (hl ? INACTIVE_HIGHLIGHTED : INACTIVE) : Color.WHITE);
         tab.obj1.setForeground(hl ? (i!=me ? Color.BLACK : ACTIVE_HIGHLIGHTED) : Color.BLACK);
      }
   }

   /** Removes all highlights from every text buffer, then adjust the TAB LABEL COLOR if necessary. */
   public void clearShade() { for(int i=0; ;i++) if (i < tabs.size()) tabs.get(i).clearShade(); else { adjustLabelColor(); break; } }

   /** Switch to the i-th tab (Note: if successful, it will always send STATUS_CHANGE to the registered listeners. */
   private void select(int i) {
      if (i < 0 || i >= tabs.size()) return; else { me=i; component.revalidate(); adjustLabelColor(); component.removeAll(); }
      if (tabs.size() > 1) component.add(tabBarScroller, BorderLayout.NORTH);
      tabs.get(me).addTo(component, BorderLayout.CENTER);
      component.repaint();
      tabs.get(me).requestFocusInWindow();
      tabBar.scrollRectToVisible(new Rectangle(0,0,0,0)); // Forces recalculation
      tabBar.scrollRectToVisible(new Rectangle(tabs.get(me).obj2.getX(), 0, tabs.get(me).obj2.getWidth()+200, 1));
      listeners.fire(this, Event.STATUS_CHANGE);
   }

   /** Refresh all tabs. */
   public void reloadAll() { for(OurSyntaxWidget t: tabs) t.reload(); }

   /** Return the list of all filenames except the filename in the i-th tab. */
   private List<String> getAllNamesExcept(int i) {
      ArrayList<String> ans = new ArrayList<String>();
      for(int x=0; ;x++) if (x == tabs.size()) return ans; else if (x != i) ans.add(tabs.get(x).getFilename());
   }

   /** Save the current tab content to the file system.
    * @param alwaysPickNewName - if true, it will always pop up a File Selection dialog box to ask for the filename
    * @return null if an error occurred (otherwise, return the filename)
    */
   public String save(boolean alwaysPickNewName) {
      if (me < 0 || me >= tabs.size() || !tabs.get(me).save(alwaysPickNewName, getAllNamesExcept(me))) return null;
      return tabs.get(me).getFilename();
   }

   /** Close the i-th tab (if there are no more tabs afterwards, we'll create a new empty tab).
    *
    * <p> If the text editor content is not modified since the last save, then return true; otherwise, ask the user.
    * <p> If the user says to save it, we will attempt to save it, then return true iff the save succeeded.
    * <p> If the user says to discard it, this method returns true.
    * <p> If the user says to cancel it, this method returns false (and the original tab and its contents will not be harmed).
    */
   private boolean close(int i) {
      clearShade();
      if (i<0 || i>=tabs.size()) return true; else if (!tabs.get(i).discard(true, getAllNamesExcept(i))) return false;
      if (tabs.size() > 1) { tabBar.remove(i);  tabs.remove(i);  if (me >= tabs.size()) me = tabs.size() - 1; }
      select(me);
      return true;
   }

   /** Close the current tab (then create a new empty tab if there were no tabs remaining) */
   public void close()  { close(me); }

   /** Close every tab then create a new empty tab; returns true iff success. */
   public boolean closeAll() {
      for(int i=tabs.size()-1; i>=0; i--) if (tabs.get(i).modified()==false) close(i); // first close all the unmodified files
      for(int i=tabs.size()-1; i>=0; i--) if (close(i)==false) return false; // then attempt to close modified files one-by-one
      return true;
   }

   /** Returns the number of tabs. */
   public int count() { return tabs.size();  }

   /** Return a modifiable map from each filename to its text content (Note: changes to the map does NOT affect this object) */
   public Map<String,String> takeSnapshot() {
      Map<String,String> map = new LinkedHashMap<String,String>();
      for(OurSyntaxWidget t: tabs) { map.put(t.getFilename(), t.getText()); }
      return map;
   }

   /** Returns the list of filenames corresponding to each text buffer. */
   public List<String> getFilenames() { return getAllNamesExcept(-1); }

   /** Changes the font name, font size, and tabsize of every text buffer. */
   public void setFont(String name, int size, int tabSize) {
      fontName=name; fontSize=size; this.tabSize=tabSize; for(OurSyntaxWidget t: tabs) t.setFont(name, size, tabSize);
   }

   /** Enables or disables syntax highlighting. */
   public void enableSyntax(boolean flag) {  syntaxHighlighting=flag;  for(OurSyntaxWidget t: tabs) t.enableSyntax(flag);  }

   /** Returns the JTextArea of the current text buffer. */
   public OurSyntaxWidget get() { return (me>=0 && me<tabs.size()) ? tabs.get(me) : new OurSyntaxWidget(); }

   /** True if the i-th text buffer has been modified since it was last loaded/saved */
   public boolean modified(int i)  { return (i>=0 && i<tabs.size()) ? tabs.get(i).modified() : false; }

   /** Switches to the previous tab. */
   public void prev() { if (tabs.size()>=2) select(me==0 ? tabs.size()-1 : (me-1)); }

   /** Switches to the next tab. */
   public void next() { if (tabs.size()>=2) select(me==tabs.size()-1 ? 0 : (me+1)); }

   /** Create a new tab with the given filename (if filename==null, we'll create a blank tab instead)
    * <p> If a text buffer with that filename already exists, we will just switch to it; else we'll read that file into a new tab.
    * @return false iff an error occurred
    */
   public boolean newtab(String filename) {
      if (filename!=null) {
         filename = Util.canon(filename);
         for(int i=0; i<tabs.size(); i++) if (tabs.get(i).getFilename().equals(filename)) { if (i!=me) select(i); return true; }
      }
      final JLabel lb = OurUtil.label("", OurUtil.getVizFont().deriveFont(Font.BOLD), Color.BLACK, Color.WHITE);
      lb.setBorder(new OurBorder(BORDER, BORDER, Color.WHITE, BORDER));
      lb.addMouseListener(new MouseAdapter() {
         @Override public void mousePressed(MouseEvent e) { for(int i=0; i<tabs.size(); i++) if (tabs.get(i).obj1 == lb) select(i); }
      });
      JPanel h1 = OurUtil.makeH(4); h1.setBorder(new OurBorder(null, null, BORDER, null));
      JPanel h2 = OurUtil.makeH(3); h2.setBorder(new OurBorder(null, null, BORDER, null));
      JPanel pan = Util.onMac() ? OurUtil.makeVL(null, 2, OurUtil.makeHB(h1, lb, h2))
                                : OurUtil.makeVL(null, 2, OurUtil.makeHB(h1, lb, h2, GRAY), GRAY);
      pan.setAlignmentX(0.0f);
      pan.setAlignmentY(1.0f);
      OurSyntaxWidget text = new OurSyntaxWidget(syntaxHighlighting, "", fontName, fontSize, tabSize, lb, pan);
      tabBar.add(pan, tabs.size());
      tabs.add(text);
      text.listeners.add(listener); // add listener AFTER we've updated this.tabs and this.tabBar
      if (filename==null) {
         text.discard(false, getFilenames()); // forces the tab to re-derive a suitable fresh name
      } else {
         if (!text.load(filename)) return false;
         for(int i=tabs.size()-1; i>=0; i--) if (!tabs.get(i).isFile() && tabs.get(i).getText().length()==0) {
            tabs.get(i).discard(false, getFilenames()); close(i); break; // Remove the rightmost untitled empty tab
         }
      }
      select(tabs.size() - 1); // Must call this to switch to the new tab; and it will fire STATUS_CHANGE message which is important
      return true;
   }

   /** Highlights the text editor, based on the location information in the set of Pos objects. */
   public void shade(Iterable<Pos> set, Color color, boolean clearOldHighlightsFirst) {
      if (clearOldHighlightsFirst) clearShade();
      OurSyntaxWidget text = null;
      int c = 0, d;
      for(Pos p: set) if (p!=null && p.filename.length()>0 && p.y>0 && p.x>0 && newtab(p.filename)) {
         text = get();
         c = text.getLineStartOffset(p.y-1) + p.x - 1;
         d = text.getLineStartOffset(p.y2-1) + p.x2 - 1;
         text.shade(color, c, d+1);
      }
      if (text!=null) { text.moveCaret(0, 0); text.moveCaret(c, c); } // Move to 0 ensures we'll scroll to the highlighted section
      get().requestFocusInWindow();
      adjustLabelColor();
      listeners.fire(this, Event.STATUS_CHANGE);
   }

   /** Highlights the text editor, based on the location information in the Pos object. */
   public void shade(Pos pos) { shade(Util.asList(pos), new Color(0.9f, 0.4f, 0.4f), true); }
}
