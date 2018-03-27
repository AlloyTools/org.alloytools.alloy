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

package edu.mit.csail.sdg.alloy4graph;

import static java.awt.Color.BLACK;
import static java.awt.Color.WHITE;
import static java.awt.event.InputEvent.BUTTON1_MASK;
import static java.awt.event.InputEvent.BUTTON3_MASK;
import static java.awt.event.InputEvent.CTRL_MASK;

import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Rectangle;
import java.awt.RenderingHints;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionAdapter;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JRadioButton;
import javax.swing.JTextField;
import javax.swing.JViewport;
import javax.swing.border.EmptyBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.OurPDFWriter;
import edu.mit.csail.sdg.alloy4.OurPNGWriter;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.Util;

/**
 * This class displays the graph.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final strictfp class GraphViewer extends JPanel {

    /** This ensures the class can be serialized reliably. */
    private static final long serialVersionUID = 0;

    /** The graph that we are displaying. */
    private final Graph       graph;

    /** The current amount of zoom. */
    private double            scale            = 1d;

    /**
     * The currently hovered GraphNode or GraphEdge or group, or null if there is
     * none.
     */
    private Object            highlight        = null;

    /**
     * The currently selected GraphNode or GraphEdge or group, or null if there is
     * none.
     */
    private Object            selected         = null;

    /**
     * The button that initialized the drag-and-drop; this value is undefined when
     * we're not currently doing drag-and-drop.
     */
    private int               dragButton       = 0;

    /**
     * The right-click context menu associated with this JPanel.
     */
    public final JPopupMenu   pop              = new JPopupMenu();

    /** Locates the node or edge at the given (X,Y) location. */
    private Object alloyFind(int mouseX, int mouseY) {
        return graph.find(scale, mouseX, mouseY);
    }

    /**
     * Returns the annotation for the node or edge at location x,y (or null if none)
     */
    public Object alloyGetAnnotationAtXY(int mouseX, int mouseY) {
        Object obj = alloyFind(mouseX, mouseY);
        if (obj instanceof GraphNode)
            return ((GraphNode) obj).uuid;
        if (obj instanceof GraphEdge)
            return ((GraphEdge) obj).uuid;
        return null;
    }

    /**
     * Returns the annotation for the currently selected node/edge (or null if none)
     */
    public Object alloyGetSelectedAnnotation() {
        if (selected instanceof GraphNode)
            return ((GraphNode) selected).uuid;
        if (selected instanceof GraphEdge)
            return ((GraphEdge) selected).uuid;
        return null;
    }

    /**
     * Returns the annotation for the currently highlighted node/edge (or null if
     * none)
     */
    public Object alloyGetHighlightedAnnotation() {
        if (highlight instanceof GraphNode)
            return ((GraphNode) highlight).uuid;
        if (highlight instanceof GraphEdge)
            return ((GraphEdge) highlight).uuid;
        return null;
    }

    /**
     * Stores the mouse positions needed to calculate drag-and-drop.
     */
    private int oldMouseX = 0, oldMouseY = 0, oldX = 0, oldY = 0;

    /** Repaint this component. */
    public void alloyRepaint() {
        Container c = getParent();
        while (c != null) {
            if (c instanceof JViewport)
                break;
            else
                c = c.getParent();
        }
        setSize((int) (graph.getTotalWidth() * scale), (int) (graph.getTotalHeight() * scale));
        if (c != null) {
            c.invalidate();
            c.repaint();
            c.validate();
        } else {
            invalidate();
            repaint();
            validate();
        }
    }

    /**
     * Construct a GraphViewer that displays the given graph.
     */
    public GraphViewer(final Graph graph) {
        OurUtil.make(this, BLACK, WHITE, new EmptyBorder(0, 0, 0, 0));
        setBorder(null);
        this.scale = graph.defaultScale;
        this.graph = graph;
        graph.layout();
        final JMenuItem zoomIn = new JMenuItem("Zoom In");
        final JMenuItem zoomOut = new JMenuItem("Zoom Out");
        final JMenuItem zoomToFit = new JMenuItem("Zoom to Fit");
        final JMenuItem print = new JMenuItem("Export to PNG or PDF");
        pop.add(zoomIn);
        pop.add(zoomOut);
        pop.add(zoomToFit);
        pop.add(print);
        ActionListener act = new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                Container c = getParent();
                while (c != null) {
                    if (c instanceof JViewport)
                        break;
                    else
                        c = c.getParent();
                }
                if (e.getSource() == print)
                    alloySaveAs();
                if (e.getSource() == zoomIn) {
                    scale = scale * 1.33d;
                    if (!(scale < 500d))
                        scale = 500d;
                }
                if (e.getSource() == zoomOut) {
                    scale = scale / 1.33d;
                    if (!(scale > 0.1d))
                        scale = 0.1d;
                }
                if (e.getSource() == zoomToFit) {
                    if (c == null)
                        return;
                    int w = c.getWidth() - 15, h = c.getHeight() - 15; // 15
                                                                      // gives
                                                                      // a
                                                                      // comfortable
                                                                      // round-off
                                                                      // margin
                    if (w <= 0 || h <= 0)
                        return;
                    double scale1 = ((double) w) / graph.getTotalWidth(),
                                    scale2 = ((double) h) / graph.getTotalHeight();
                    if (scale1 < scale2)
                        scale = scale1;
                    else
                        scale = scale2;
                }
                alloyRepaint();
            }
        };
        zoomIn.addActionListener(act);
        zoomOut.addActionListener(act);
        zoomToFit.addActionListener(act);
        print.addActionListener(act);
        addMouseMotionListener(new MouseMotionAdapter() {

            @Override
            public void mouseMoved(MouseEvent ev) {
                if (pop.isVisible())
                    return;
                Object obj = alloyFind(ev.getX(), ev.getY());
                if (highlight != obj) {
                    highlight = obj;
                    alloyRepaint();
                }
            }

            @Override
            public void mouseDragged(MouseEvent ev) {
                if (selected instanceof GraphNode && dragButton == 1) {
                    int newX = (int) (oldX + (ev.getX() - oldMouseX) / scale);
                    int newY = (int) (oldY + (ev.getY() - oldMouseY) / scale);
                    GraphNode n = (GraphNode) selected;
                    if (n.x() != newX || n.y() != newY) {
                        n.tweak(newX, newY);
                        alloyRepaint();
                        scrollRectToVisible(new Rectangle((int) ((newX - graph.getLeft()) * scale) - n.getWidth() / 2 - 5, (int) ((newY - graph.getTop()) * scale) - n.getHeight() / 2 - 5, n.getWidth() + n.getReserved() + 10, n.getHeight() + 10));
                    }
                }
            }
        });
        addMouseListener(new MouseAdapter() {

            @Override
            public void mouseReleased(MouseEvent ev) {
                Object obj = alloyFind(ev.getX(), ev.getY());
                graph.recalcBound(true);
                selected = null;
                highlight = obj;
                alloyRepaint();
            }

            @Override
            public void mousePressed(MouseEvent ev) {
                dragButton = 0;
                int mod = ev.getModifiers();
                if ((mod & BUTTON3_MASK) != 0) {
                    selected = alloyFind(ev.getX(), ev.getY());
                    highlight = null;
                    alloyRepaint();
                    pop.show(GraphViewer.this, ev.getX(), ev.getY());
                } else if ((mod & BUTTON1_MASK) != 0 && (mod & CTRL_MASK) != 0) {
                    // This lets Ctrl+LeftClick bring up the popup menu, just
                    // like RightClick,
                    // since many Mac mouses do not have a right button.
                    selected = alloyFind(ev.getX(), ev.getY());
                    highlight = null;
                    alloyRepaint();
                    pop.show(GraphViewer.this, ev.getX(), ev.getY());
                } else if ((mod & BUTTON1_MASK) != 0) {
                    dragButton = 1;
                    selected = alloyFind(oldMouseX = ev.getX(), oldMouseY = ev.getY());
                    highlight = null;
                    alloyRepaint();
                    if (selected instanceof GraphNode) {
                        oldX = ((GraphNode) selected).x();
                        oldY = ((GraphNode) selected).y();
                    }
                }
            }

            @Override
            public void mouseExited(MouseEvent ev) {
                if (highlight != null) {
                    highlight = null;
                    alloyRepaint();
                }
            }
        });
    }

    /**
     * This color is used as the background for a JTextField that contains bad data.
     * <p>
     * Note: we intentionally choose to make it an instance field rather than a
     * static field, since we want to make sure we only instantiate it from the AWT
     * Event Dispatching thread.
     */
    private final Color            badColor  = new Color(255, 200, 200);

    /**
     * This synchronized field stores the most recent DPI value.
     */
    private static volatile double oldDPI    = 72;

    /**
     * True if we are currently in the middle of a DocumentListener already.
     */
    private boolean                recursive = false;

    /**
     * This updates the three input boxes and the three accompanying text labels,
     * then return the width in pixels.
     */
    private int alloyRefresh(int who, double ratio, JTextField w1, JLabel w2, JTextField h1, JLabel h2, JTextField d1, JLabel d2, JLabel msg) {
        if (recursive)
            return 0;
        try {
            recursive = true;
            w1.setBackground(WHITE);
            h1.setBackground(WHITE);
            d1.setBackground(WHITE);
            boolean bad = false;
            double w;
            try {
                w = Double.parseDouble(w1.getText());
            } catch (NumberFormatException ex) {
                w = 0;
            }
            double h;
            try {
                h = Double.parseDouble(h1.getText());
            } catch (NumberFormatException ex) {
                h = 0;
            }
            double d;
            try {
                d = Double.parseDouble(d1.getText());
            } catch (NumberFormatException ex) {
                d = 0;
            }
            if (who == 1) {
                h = ((int) (w * 100 / ratio)) / 100D;
                h1.setText("" + h);
            } // Maintains aspect ratio
            if (who == 2) {
                w = ((int) (h * 100 * ratio)) / 100D;
                w1.setText("" + w);
            } // Maintains aspect ratio
            if (!(d >= 0.01) || !(d <= 10000)) {
                bad = true;
                d1.setBackground(badColor);
                msg.setText("DPI must be between 0.01 and 10000");
            }
            if (!(h >= 0.01) || !(h <= 10000)) {
                bad = true;
                h1.setBackground(badColor);
                msg.setText("Height must be between 0.01 and 10000");
                if (who == 1)
                    h1.setText("");
            }
            if (!(w >= 0.01) || !(w <= 10000)) {
                bad = true;
                w1.setBackground(badColor);
                msg.setText("Width must be between 0.01 and 10000");
                if (who == 2)
                    w1.setText("");
            }
            if (bad) {
                w2.setText(" inches");
                h2.setText(" inches");
                return 0;
            } else
                msg.setText(" ");
            w2.setText(" inches (" + (int) (w * d) + " pixels)");
            h2.setText(" inches (" + (int) (h * d) + " pixels)");
            return (int) (w * d);
        } finally {
            recursive = false;
        }
    }

    /**
     * Export the current drawing as a PNG or PDF file by asking the user for the
     * filename and the image resolution.
     */
    public void alloySaveAs() {
        // Figure out the initial width, height, and DPI that we might want to
        // suggest to the user
        final double ratio = ((double) (graph.getTotalWidth())) / graph.getTotalHeight();
        double dpi, iw = 8.5D, ih = ((int) (iw * 100 / ratio)) / 100D; // First
                                                                      // set
                                                                      // the
                                                                      // width
                                                                      // to be
                                                                      // 8.5inch
                                                                      // and
                                                                      // compute
                                                                      // height
                                                                      // accordingly
        if (ih > 11D) {
            ih = 11D;
            iw = ((int) (ih * 100 * ratio)) / 100D;
        } // If too tall, then set height=11inch, and compute width accordingly
        synchronized (GraphViewer.class) {
            dpi = oldDPI;
        }
        // Prepare the dialog box
        final JLabel msg = OurUtil.label(" ", Color.RED);
        final JLabel w = OurUtil.label("Width: " + ((int) (graph.getTotalWidth() * scale)) + " pixels");
        final JLabel h = OurUtil.label("Height: " + ((int) (graph.getTotalHeight() * scale)) + " pixels");
        final JTextField w1 = new JTextField("" + iw);
        final JLabel w0 = OurUtil.label("Width: "), w2 = OurUtil.label("");
        final JTextField h1 = new JTextField("" + ih);
        final JLabel h0 = OurUtil.label("Height: "), h2 = OurUtil.label("");
        final JTextField d1 = new JTextField("" + (int) dpi);
        final JLabel d0 = OurUtil.label("Resolution: "), d2 = OurUtil.label(" dots per inch");
        final JTextField dp1 = new JTextField("" + (int) dpi);
        final JLabel dp0 = OurUtil.label("Resolution: "), dp2 = OurUtil.label(" dots per inch");
        alloyRefresh(0, ratio, w1, w2, h1, h2, d1, d2, msg);
        Dimension dim = new Dimension(100, 20);
        w1.setMaximumSize(dim);
        w1.setPreferredSize(dim);
        w1.setEnabled(false);
        h1.setMaximumSize(dim);
        h1.setPreferredSize(dim);
        h1.setEnabled(false);
        d1.setMaximumSize(dim);
        d1.setPreferredSize(dim);
        d1.setEnabled(false);
        dp1.setMaximumSize(dim);
        dp1.setPreferredSize(dim);
        dp1.setEnabled(false);
        w1.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void changedUpdate(DocumentEvent e) {
                alloyRefresh(1, ratio, w1, w2, h1, h2, d1, d2, msg);
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                changedUpdate(null);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                changedUpdate(null);
            }
        });
        h1.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void changedUpdate(DocumentEvent e) {
                alloyRefresh(2, ratio, w1, w2, h1, h2, d1, d2, msg);
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                changedUpdate(null);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                changedUpdate(null);
            }
        });
        d1.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void changedUpdate(DocumentEvent e) {
                alloyRefresh(3, ratio, w1, w2, h1, h2, d1, d2, msg);
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                changedUpdate(null);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                changedUpdate(null);
            }
        });
        final JRadioButton b1 = new JRadioButton("As a PNG with the window's current magnification:", true);
        final JRadioButton b2 = new JRadioButton("As a PNG with a specific width, height, and resolution:", false);
        final JRadioButton b3 = new JRadioButton("As a PDF with the given resolution:", false);
        b1.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                b2.setSelected(false);
                b3.setSelected(false);
                if (!b1.isSelected())
                    b1.setSelected(true);
                w1.setEnabled(false);
                h1.setEnabled(false);
                d1.setEnabled(false);
                dp1.setEnabled(false);
                msg.setText(" ");
                w1.setBackground(WHITE);
                h1.setBackground(WHITE);
                d1.setBackground(WHITE);
            }
        });
        b2.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                b1.setSelected(false);
                b3.setSelected(false);
                if (!b2.isSelected())
                    b2.setSelected(true);
                w1.setEnabled(true);
                h1.setEnabled(true);
                d1.setEnabled(true);
                dp1.setEnabled(false);
                msg.setText(" ");
                alloyRefresh(1, ratio, w1, w2, h1, h2, d1, d2, msg);
            }
        });
        b3.addActionListener(new ActionListener() {

            @Override
            public void actionPerformed(ActionEvent e) {
                b1.setSelected(false);
                b2.setSelected(false);
                if (!b3.isSelected())
                    b3.setSelected(true);
                w1.setEnabled(false);
                h1.setEnabled(false);
                d1.setEnabled(false);
                dp1.setEnabled(true);
                msg.setText(" ");
                w1.setBackground(WHITE);
                h1.setBackground(WHITE);
                d1.setBackground(WHITE);
            }
        });
        // Ask whether the user wants to change the width, height, and DPI
        double myScale;
        while (true) {
            if (!OurDialog.getInput("Export as PNG or PDF", new Object[] {
                                                                          b1, OurUtil.makeH(20, w, null), OurUtil.makeH(20, h, null), " ", b2, OurUtil.makeH(20, w0, w1, w2, null), OurUtil.makeH(20, h0, h1, h2, null), OurUtil.makeH(20, d0, d1, d2, null), OurUtil.makeH(20, msg, null), b3, OurUtil.makeH(20, dp0, dp1, dp2, null)
            }))
                return;
            // Let's validate the values
            if (b2.isSelected()) {
                int widthInPixel = alloyRefresh(3, ratio, w1, w2, h1, h2, d1, d2, msg);
                String err = msg.getText().trim();
                if (err.length() > 0)
                    continue;
                dpi = Double.parseDouble(d1.getText());
                myScale = ((double) widthInPixel) / graph.getTotalWidth();
                int heightInPixel = (int) (graph.getTotalHeight() * myScale);
                if (widthInPixel > 4000 || heightInPixel > 4000)
                    if (!OurDialog.yesno("The image dimension (" + widthInPixel + "x" + heightInPixel + ") is very large. Are you sure?"))
                        continue;
            } else if (b3.isSelected()) {
                try {
                    dpi = Double.parseDouble(dp1.getText());
                } catch (NumberFormatException ex) {
                    dpi = (-1);
                }
                if (dpi < 50 || dpi > 3000) {
                    OurDialog.alert("The DPI must be between 50 and 3000.");
                    continue;
                }
                myScale = 0; // This field is unused for PDF generation
            } else {
                dpi = 72;
                myScale = scale;
            }
            break;
        }
        // Ask the user for a filename
        File filename;
        if (b3.isSelected())
            filename = OurDialog.askFile(false, null, ".pdf", "PDF file");
        else
            filename = OurDialog.askFile(false, null, ".png", "PNG file");
        if (filename == null)
            return;
        if (filename.exists() && !OurDialog.askOverwrite(filename.getAbsolutePath()))
            return;
        // Attempt to write the PNG or PDF file
        try {
            System.gc(); // Try to avoid possible premature out-of-memory
                        // exceptions
            if (b3.isSelected())
                alloySaveAsPDF(filename.getAbsolutePath(), (int) dpi);
            else
                alloySaveAsPNG(filename.getAbsolutePath(), myScale, dpi, dpi);
            synchronized (GraphViewer.class) {
                oldDPI = dpi;
            }
            Util.setCurrentDirectory(filename.getParentFile());
        } catch (Throwable ex) {
            OurDialog.alert("An error has occured in writing the output file:\n" + ex);
        }
    }

    /**
     * Export the current drawing as a PDF file with the given image resolution.
     */
    public void alloySaveAsPDF(String filename, int dpi) throws IOException {
        try {
            double xwidth = dpi * 8L + (dpi / 2L); // Width is up to 8.5 inch
            double xheight = dpi * 11L; // Height is up to 11 inch
            double scale1 = (xwidth - dpi) / graph.getTotalWidth(); // We leave
                                                                   // 0.5 inch
                                                                   // on the
                                                                   // left and
                                                                   // right
            double scale2 = (xheight - dpi) / graph.getTotalHeight(); // We
                                                                     // leave
                                                                     // 0.5
                                                                     // inch
                                                                     // on
                                                                     // the
                                                                     // left
                                                                     // and
                                                                     // right
            if (scale1 < scale2)
                scale2 = scale1; // Choose the scale such that the image does
                                // not exceed the page in either direction
            OurPDFWriter x = new OurPDFWriter(filename, dpi, scale2);
            graph.draw(new Artist(x), scale2, null, false);
            x.close();
        } catch (Throwable ex) {
            if (ex instanceof IOException)
                throw (IOException) ex;
            throw new IOException("Failure writing the PDF file to " + filename + " (" + ex + ")");
        }
    }

    /**
     * Export the current drawing as a PNG file with the given file name and image
     * resolution.
     */
    public void alloySaveAsPNG(String filename, double scale, double dpiX, double dpiY) throws IOException {
        try {
            int width = (int) (graph.getTotalWidth() * scale);
            if (width < 10)
                width = 10;
            int height = (int) (graph.getTotalHeight() * scale);
            if (height < 10)
                height = 10;
            BufferedImage bf = new BufferedImage(width, height, BufferedImage.TYPE_INT_RGB);
            Graphics2D gr = (Graphics2D) (bf.getGraphics());
            gr.setColor(WHITE);
            gr.fillRect(0, 0, width, height);
            gr.setColor(BLACK);
            gr.scale(scale, scale);
            gr.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            graph.draw(new Artist(gr), scale, null, false);
            OurPNGWriter.writePNG(bf, filename, dpiX, dpiY);
        } catch (Throwable ex) {
            if (ex instanceof IOException)
                throw (IOException) ex;
            throw new IOException("Failure writing the PNG file to " + filename + " (" + ex + ")");
        }
    }

    /** Show the popup menu at location (x,y) */
    public void alloyPopup(Component c, int x, int y) {
        pop.show(c, x, y);
    }

    /** Returns a DOT representation of the current graph. */
    @Override
    public String toString() {
        return graph.toString();
    }

    /** Returns the preferred size of this component. */
    @Override
    public Dimension getPreferredSize() {
        return new Dimension((int) (graph.getTotalWidth() * scale), (int) (graph.getTotalHeight() * scale));
    }

    /**
     * This method is called by Swing to draw this component.
     */
    @Override
    public void paintComponent(final Graphics gr) {
        super.paintComponent(gr);
        Graphics2D g2 = (Graphics2D) gr;
        AffineTransform oldAF = (AffineTransform) (g2.getTransform().clone());
        g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        g2.scale(scale, scale);
        Object sel = (selected != null ? selected : highlight);
        GraphNode c = null;
        if (sel instanceof GraphNode && ((GraphNode) sel).shape() == null) {
            c = (GraphNode) sel;
            sel = c.ins.get(0);
        }
        graph.draw(new Artist(g2), scale, sel, true);
        if (c != null) {
            gr.setColor(((GraphEdge) sel).color());
            gr.fillArc(c.x() - 5 - graph.getLeft(), c.y() - 5 - graph.getTop(), 10, 10, 0, 360);
        }
        g2.setTransform(oldAF);
    }
}
