package edu.mit.csail.sdg.alloy4;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.CaretListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.Element;
import javax.swing.text.JTextComponent;
import javax.swing.text.Utilities;
import java.awt.*;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;

public class LineNumbersView extends JComponent implements DocumentListener, CaretListener, ComponentListener {

    private static final int LINE_NUMBERS_MARGIN_PX_WIDTH = 28; // better way than pixels?  based on font size?
    private int displayWidth = 0;
    private boolean display = false;

    private static final long serialVersionUID = 1L;

    private JTextComponent editor;
    private Font font;

    public LineNumbersView(JTextComponent editor, boolean shouldDisplay) {
        this.editor = editor;

        if ( shouldDisplay ) {
            display = true;
            displayWidth = LINE_NUMBERS_MARGIN_PX_WIDTH;
            editor.getDocument().addDocumentListener(this);
            editor.addComponentListener(this);
            editor.addCaretListener(this);
        } else {
            display = false;
            displayWidth = 0;
        }
    }

    @Override
    public void paintComponent(Graphics g) {
        super.paintComponent(g);

        if ( display ) {

            Rectangle clip = g.getClipBounds();
            int startOffset = editor.viewToModel(new Point(0, clip.y));
            int endOffset = editor.viewToModel(new Point(0, clip.y + clip.height));

            while (startOffset <= endOffset) {
                try {
                    String lineNumber = getLineNumber(startOffset);
                    if (lineNumber != null) {
                        int x = getInsets().left + 2;
                        int y = getOffsetY(startOffset);

                        font = font != null ?
                                font :
                                new Font(editor.getFont().getName(), Font.PLAIN, editor.getFont().getSize());
                        g.setFont(font);
                        g.setColor(isCurrentLine(startOffset) ? Color.RED : Color.BLACK);
                        g.drawString(lineNumber, x, y);
                    }
                    startOffset = Utilities.getRowEnd(editor, startOffset) + 1;
                } catch (BadLocationException e) {
                    e.printStackTrace();
                }
            }
        }
    }
    private String getLineNumber(int offset) {
        Element root = editor.getDocument().getDefaultRootElement();
        int index = root.getElementIndex(offset);
        Element line = root.getElement(index);

        // how long are alloy specifications often?
        return line.getStartOffset() == offset ? String.format("%3d", index + 1) : null;
    }

    private int getOffsetY(int offset) throws BadLocationException {
        FontMetrics fontMetrics = editor.getFontMetrics(editor.getFont());
        int descent = fontMetrics.getDescent();

        Rectangle r = editor.modelToView(offset);
        return r.y + r.height - descent;
    }

    private boolean isCurrentLine(int offset) {
        int caretPosition = editor.getCaretPosition();
        Element root = editor.getDocument().getDefaultRootElement();
        return root.getElementIndex(offset) == root.getElementIndex(caretPosition);
    }

    private void documentChanged() {
        SwingUtilities.invokeLater(() -> {
            repaint();
        });
    }

    private void updateSize() {
        Dimension size = new Dimension(displayWidth, editor.getHeight());
        setPreferredSize(size);
        setSize(size);
    }

    @Override
    public void insertUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void changedUpdate(DocumentEvent e) {
        documentChanged();
    }

    @Override
    public void caretUpdate(CaretEvent e) {
        documentChanged();
    }

    @Override
    public void componentResized(ComponentEvent e) {
        updateSize();
        documentChanged();
    }

    @Override
    public void componentMoved(ComponentEvent e) {
    }

    @Override
    public void componentShown(ComponentEvent e) {
        updateSize();
        documentChanged();
    }

    @Override
    public void componentHidden(ComponentEvent e) {
    }

    public void enableLineNumbers(boolean flag) {
        display = flag;
        if ( display ) {
            displayWidth = LINE_NUMBERS_MARGIN_PX_WIDTH;
        } else {
            displayWidth = 0;
        }
        updateSize();
        documentChanged();
    }
}