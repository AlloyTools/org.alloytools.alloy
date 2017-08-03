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
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionListener;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.image.BufferedImage;
import java.net.URL;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;
import javax.swing.event.MenuEvent;
import javax.swing.event.MenuListener;
import javax.swing.plaf.basic.BasicSplitPaneUI;

/** Graphical convenience methods.
 *
 * <p><b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class OurUtil {

   /** This constructor is private, since this utility class never needs to be instantiated. */
   private OurUtil() { }

   /** Assign the given attributes to the given JComponent, then return the JComponent again.
    * <p> If <b>Font</b>      x is given in the list, we call obj.setFont(x)
    * <p> If <b>String</b>    x is given in the list, we call obj.setToolTipText(x)
    * <p> If <b>Border</b>    x is given in the list, we call obj.setBorder(x)
    * <p> If <b>Dimension</b> x is given in the list, we call obj.setPreferredSize(x)
    * <p> If <b>Color</b> x is given in the list, and it's the first color, we call obj.setForeground(x)
    * <p> If <b>Color</b> x is given in the list, and it's not the first color, we call obj.setBackground(x) then obj.setOpaque(true)
    * <p> (If no Font is given, then after all these changes have been applied, we will call obj.setFont() will a default font)
    */
   public static<X extends JComponent> X make(X obj, Object... attributes) {
      boolean hasFont = false, hasForeground = false;
      if (attributes!=null) for(Object x: attributes) {
         if (x instanceof Font) { obj.setFont((Font)x); hasFont=true; }
         if (x instanceof String) { obj.setToolTipText((String)x); }
         if (x instanceof Border) { obj.setBorder((Border)x); }
         if (x instanceof Dimension) { obj.setPreferredSize((Dimension)x); }
         if (x instanceof Color && !hasForeground) { obj.setForeground((Color)x); hasForeground=true; continue; }
         if (x instanceof Color) { obj.setBackground((Color)x); obj.setOpaque(true); }
      }
      if (!hasFont) obj.setFont(getVizFont());
      return obj;
   }

   /** Make a JLabel, then call Util.make() to apply a set of attributes to it.
    * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make OurUtil.make(component, attributes...)}
    */
   public static JLabel label (String label, Object... attributes)  { return make(new JLabel(label), attributes); }

   /** Make a JTextField with the given text and number of columns, then call Util.make() to apply a set of attributes to it.
    * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make OurUtil.make(component, attributes...)}
    */
   public static JTextField textfield (String text, int columns, Object... attributes)  {
      return make(new JTextField(text, columns), attributes);
   }

   /** Make a JTextArea with the given text and number of rows and columns, then call Util.make() to apply a set of attributes to it.
    * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make OurUtil.make(component, attributes...)}
    */
   public static JTextArea textarea (String text, int rows, int columns, boolean editable, boolean wrap, Object... attributes) {
      JTextArea ans = make(new JTextArea(text, rows, columns), Color.BLACK, Color.WHITE, new EmptyBorder(0,0,0,0));
      ans.setEditable(editable);
      ans.setLineWrap(wrap);
      ans.setWrapStyleWord(wrap);
      return make(ans, attributes);
   }

   /** Make a JScrollPane containing the given component (which can be null), then apply a set of attributes to it.
    * @param attributes - see {@link edu.mit.csail.sdg.alloy4.OurUtil#make OurUtil.make(component, attributes...)}
    */
   public static JScrollPane scrollpane (Component component, Object... attributes) {
      JScrollPane ans = make(new JScrollPane(), new EmptyBorder(0,0,0,0));
      if (component!=null) ans.setViewportView(component);
      ans.setMinimumSize(new Dimension(50, 50));
      return make(ans, attributes);
   }

   /** Returns the recommended font to use in the visualizer, based on the OS. */
   public static Font getVizFont()  {
      return Util.onMac() ? new Font("Lucida Grande", Font.PLAIN, 11) : new Font("Dialog", Font.PLAIN, 12);
   }

   /** Returns the screen width (in pixels). */
   public static int getScreenWidth()  { return Toolkit.getDefaultToolkit().getScreenSize().width; }

   /** Returns the screen height (in pixels). */
   public static int getScreenHeight()  { return Toolkit.getDefaultToolkit().getScreenSize().height; }

   /** Make a graphical button
    * @param label - the text to show beneath the button
    * @param tip - the tooltip to show when the mouse hovers over the button
    * @param iconFileName - if nonnull, it's the filename of the icon to show (it will be loaded from an accompanying jar file)
    * @param func - if nonnull, it's the function to call when the button is pressed
    */
   public static JButton button (String label, String tip, String iconFileName, ActionListener func) {
      JButton button = new JButton(label, (iconFileName!=null && iconFileName.length()>0) ? loadIcon(iconFileName) : null);
      if (func != null) button.addActionListener(func);
      button.setVerticalTextPosition(JButton.BOTTOM);
      button.setHorizontalTextPosition(JButton.CENTER);
      button.setBorderPainted(false);
      button.setFocusable(false);
      if (!Util.onMac()) button.setBackground(new Color(0.9f, 0.9f, 0.9f));
      button.setFont(button.getFont().deriveFont(10.0f));
      if (tip != null && tip.length() > 0) button.setToolTipText(tip);
      return button;
   }

   /** Load the given image file from an accompanying JAR file, and return it as an Icon object. */
   public static Icon loadIcon(String pathname) {
      URL url = OurUtil.class.getClassLoader().getResource(pathname);
      if (url!=null) return new ImageIcon(Toolkit.getDefaultToolkit().createImage(url));
      return new ImageIcon(new BufferedImage(1, 1, BufferedImage.TYPE_INT_RGB));
   }

   /** Make a JPanel with horizontal or vertical BoxLayout, then add the list of components to it (each aligned by xAlign and yAlign)
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   private static JPanel makeBox(boolean horizontal, float xAlign, float yAlign, Object[] components) {
      JPanel ans = new JPanel();
      ans.setLayout(new BoxLayout(ans, horizontal ? BoxLayout.X_AXIS : BoxLayout.Y_AXIS));
      ans.setAlignmentX(0.0f);
      ans.setAlignmentY(0.0f);
      Color color = null;
      for(Object x: components) {
         Component c = null;
         if (x instanceof Color) { color = (Color)x; ans.setBackground(color); continue; }
         if (x instanceof Dimension) { ans.setPreferredSize((Dimension)x); ans.setMaximumSize((Dimension)x); continue; }
         if (x instanceof Component) { c = (Component)x; }
         if (x instanceof String) { c = label((String)x, Color.BLACK); }
         if (x instanceof Integer) { int i = (Integer)x; c = Box.createRigidArea(new Dimension(horizontal?i:1, horizontal?1:i)); }
         if (x==null) { c = horizontal ? Box.createHorizontalGlue() : Box.createVerticalGlue(); }
         if (c==null) continue;
         if (color!=null) c.setBackground(color);
         if (c instanceof JComponent) { ((JComponent)c).setAlignmentX(xAlign); ((JComponent)c).setAlignmentY(yAlign); }
         ans.add(c);
      }
      return ans;
   }

   /** Make a JPanel using horizontal BoxLayout, and add the components to it (each component will be center-aligned).
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   public static JPanel makeH(Object... components) { return makeBox(true, 0.5f, 0.5f, components); }

   /** Make a JPanel using horizontal BoxLayout, and add the components to it (each component will be top-aligned).
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   public static JPanel makeHT(Object... components) { return makeBox(true, 0.5f, 0.0f, components); }

   /** Make a JPanel using horizontal BoxLayout, and add the components to it (each component will be bottom-aligned).
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   public static JPanel makeHB(Object... components) { return makeBox(true, 0.5f, 1.0f, components); }

   /** Make a JPanel using vertical BoxLayout, and add the components to it (each component will be left-aligned).
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   public static JPanel makeVL(Object... components) { return makeBox(false, 0.0f, 0.5f, components); }

   /** Make a JPanel using vertical BoxLayout, and add the components to it (each component will be right-aligned).
    * <br> If a component is Color, it's the background of this JPanel and every component after it (until we see another Color)
    * <br> If a component is Dimension, we will set it as the newly constructed JPanel's preferedSize and MaximumSize.
    * <br> If a component is String, we will insert a JLabel with it as the label.
    * <br> If a component is Integer, we will insert an "n*1" (or "1*n") rigid area instead.
    * <br> If a component is null, we will insert a horizontal (or vertical) glue instead.
    */
   public static JPanel makeVR(Object... components) { return makeBox(false, 1.0f, 0.5f, components); }

   /** Constructs a new SplitPane containing the two components given as arguments
    * @param orientation - the orientation (HORIZONTAL_SPLIT or VERTICAL_SPLIT)
    * @param first - the left component (if horizontal) or top component (if vertical)
    * @param second - the right component (if horizontal) or bottom component (if vertical)
    * @param initialDividerLocation - the initial divider location (in pixels)
    */
   public static JSplitPane splitpane (int orientation, Component first, Component second, int initialDividerLocation) {
      JSplitPane x = make(new JSplitPane(orientation, first, second), new EmptyBorder(0,0,0,0));
      x.setContinuousLayout(true);
      x.setDividerLocation(initialDividerLocation);
      x.setOneTouchExpandable(false);
      x.setResizeWeight(0.5);
      if (Util.onMac() && (x.getUI() instanceof BasicSplitPaneUI)) {
         boolean h = (orientation != JSplitPane.HORIZONTAL_SPLIT);
         ((BasicSplitPaneUI)(x.getUI())).getDivider().setBorder(new OurBorder(h,h,h,h));  // Makes the border look nicer on Mac OS X
      }
      return x;
   }

   /** Convenience method that recursively enables every JMenu and JMenuItem inside "menu".
    * @param menu - the menu to start the recursive search
    */
   public static void enableAll (JMenu menu) {
      for(int i = 0; i < menu.getMenuComponentCount(); i++) {
         Component x = menu.getMenuComponent(i);
         if (x instanceof JMenuItem) ((JMenuItem)x).setEnabled(true); else if (x instanceof JMenu) enableAll((JMenu)x);
      }
   }

   /** Construct a new JMenu and add it to an existing JMenuBar.
    * <p> Note: every time the user expands then collapses this JMenu, we automatically enable all JMenu and JMenuItem objects in it.
    *
    * @param parent - the JMenuBar to add this Menu into (or null if we don't want to add it to a JMenuBar yet)
    * @param label - the label to show on screen (if it contains '&' followed by 'a'..'z', we'll remove '&' and use it as mnemonic)
    * @param func - if nonnull we'll call its "run()" method right before expanding this menu
    */
   public static JMenu menu (JMenuBar parent, String label, final Runnable func) {
      final JMenu x = new JMenu(label.replace("&", ""), false);
      if (!Util.onMac()) {
         int i = label.indexOf('&');
         if (i>=0 && i+1<label.length()) i = label.charAt(i+1);
         if (i>='a' && i<='z') x.setMnemonic((i-'a')+'A'); else if (i>='A' && i<='Z') x.setMnemonic(i);
      }
      x.addMenuListener(new MenuListener() {
         public void menuSelected   (MenuEvent e) { if (func != null) func.run(); }
         public void menuDeselected (MenuEvent e) { OurUtil.enableAll(x); }
         public void menuCanceled   (MenuEvent e) { OurUtil.enableAll(x); }
      });
      if (parent!=null) parent.add(x);
      return x;
   }

   /** Construct a new JMenuItem then add it to an existing JMenu.
    * @param parent - the JMenu to add this JMenuItem into (or null if you don't want to add it to any JMenu yet)
    * @param label - the text to show on the menu
    * @param attrs - a list of attributes to apply onto the new JMenuItem
    * <p> If one positive number  a is supplied, we call setMnemonic(a)
    * <p> If two positive numbers a and b are supplied, and a!=VK_ALT, and a!=VK_SHIFT, we call setMnemoic(a) and setAccelerator(b)
    * <p> If two positive numbers a and b are supplied, and a==VK_ALT or a==VK_SHIFT, we call setAccelerator(a | b)
    * <p> If an ActionListener is supplied, we call addActionListener(x)
    * <p> If an Boolean x      is supplied, we call setEnabled(x)
    * <p> If an Icon x         is supplied, we call setIcon(x)
    */
   public static JMenuItem menuItem (JMenu parent, String label, Object... attrs) {
      JMenuItem m = new JMenuItem(label, null);
      int accelMask = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
      boolean hasMnemonic = false;
      for(Object x: attrs) {
         if (x instanceof Character || x instanceof Integer) {
            int k = (x instanceof Character) ? ((int)((Character)x)) : ((Integer)x).intValue();
            if (k < 0) continue;
            if (k==KeyEvent.VK_ALT)   { hasMnemonic = true; accelMask = accelMask | InputEvent.ALT_MASK;   continue; }
            if (k==KeyEvent.VK_SHIFT) { hasMnemonic = true; accelMask = accelMask | InputEvent.SHIFT_MASK; continue; }
            if (!hasMnemonic) { m.setMnemonic(k); hasMnemonic=true; } else m.setAccelerator(KeyStroke.getKeyStroke(k, accelMask));
         }
         if (x instanceof ActionListener) m.addActionListener((ActionListener)x);
         if (x instanceof Icon) m.setIcon((Icon)x);
         if (x instanceof Boolean) m.setEnabled((Boolean)x);
      }
      if (parent!=null) parent.add(m);
      return m;
   }
   
   /** This method minimizes the window. */
   public static void minimize(JFrame frame) { frame.setExtendedState(JFrame.ICONIFIED); }

   /** This method alternatingly maximizes or restores the window. */
   public static void zoom(JFrame frame) {
      int both = JFrame.MAXIMIZED_BOTH;
      frame.setExtendedState((frame.getExtendedState() & both)!=both ? both : JFrame.NORMAL);
   }

   /** Make the frame visible, non-iconized, and focused. */
   public static void show(JFrame frame) {
      frame.setVisible(true);
      frame.setExtendedState(frame.getExtendedState() & ~JFrame.ICONIFIED);
      frame.requestFocus();
      frame.toFront();
   }

   public static JPanel makeGrid(int cols, GridBagConstraints template, Container... containers) {
      JPanel ans = new JPanel(new GridBagLayout());
      int i = -1;
      for (Container container : containers) {
         for (Component comp : container.getComponents()) {
            i++;
            GridBagConstraints c = (GridBagConstraints) template.clone();
            c.gridx = i % cols;
            c.gridy = i / cols;
            ans.add(comp, c);
         }
      }
      return ans;
   }

   /** Simple builder class for building GridBagConstraints objects */
   public static class GridBagConstraintsBuilder {
      private final GridBagConstraints gbc;

      /** Constructor */ 
      public GridBagConstraintsBuilder() { this.gbc = new GridBagConstraints(); }
      
      /** Returns the built GridBagConstraints instance */
      public GridBagConstraints make() { return this.gbc; }
      
      /** @see GridBagConstraints#anchor} */     
      public GridBagConstraintsBuilder anchor(int a)     { gbc.anchor = a; return this; }
      /** @see GridBagConstraints#fill */       
      public GridBagConstraintsBuilder fill(int a)       { gbc.fill = a; return this; }
      /** @see GridBagConstraints#gridheight */ 
      public GridBagConstraintsBuilder gridheight(int a) { gbc.gridheight = a; return this; }
      /** @see GridBagConstraints#gridwidth */  
      public GridBagConstraintsBuilder gridwidth(int a)  { gbc.gridwidth = a; return this; }
      /** @see GridBagConstraints#gridx */      
      public GridBagConstraintsBuilder gridx(int a)      { gbc.gridx = a; return this; }
      /** @see GridBagConstraints#gridy */      
      public GridBagConstraintsBuilder gridy(int a)      { gbc.gridy = a; return this; }
      /** @see GridBagConstraints#insets */     
      public GridBagConstraintsBuilder insets(Insets a)  { gbc.insets = a; return this; }
      /** @see GridBagConstraints#ipadx */      
      public GridBagConstraintsBuilder ipadx(int a)      { gbc.ipadx = a; return this; }
      /** @see GridBagConstraints#ipady */      
      public GridBagConstraintsBuilder ipady(int a)      { gbc.ipady = a; return this; }
      /** @see GridBagConstraints#weightx */    
      public GridBagConstraintsBuilder weightx(int a)    { gbc.weightx = a; return this; }
      /** @see GridBagConstraints#weighty */    
      public GridBagConstraintsBuilder weighty(int a)    { gbc.weighty = a; return this; }
      
      /**
       * Applies gridx(x).gridy(y)
       * 
       * @see GridBagConstraints#gridx
       * @see GridBagConstraints#gridy
       */        
      public GridBagConstraintsBuilder pos(int x, int y)     { return gridx(x).gridy(y); }
      
      
      /** 
       * Applies weightx(x).weighty(y)
       * 
       * @see GridBagConstraints#weightx 
       * @see GridBagConstraints#weighty
       */    
      public GridBagConstraintsBuilder weights(int x, int y) { return weightx(x).weighty(y); }
      
      /** 
       * Applies ipadx(x).ipday(y)
       * 
       * @see GridBagConstraints#ipadx 
       * @see GridBagConstraints#ipady
       */    
      public GridBagConstraintsBuilder ipads(int x, int y)   { return ipadx(x).ipady(y); }
   }
}
