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

import static javax.swing.JOptionPane.ERROR_MESSAGE;
import static javax.swing.JOptionPane.QUESTION_MESSAGE;
import static javax.swing.JOptionPane.WARNING_MESSAGE;
import static javax.swing.JOptionPane.YES_NO_OPTION;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.FileDialog;
import java.awt.Font;
import java.awt.Frame;
import java.awt.GraphicsEnvironment;
import java.awt.HeadlessException;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.io.File;
import java.io.FilenameFilter;
import java.util.Locale;
import java.util.Objects;

import javax.swing.DefaultComboBoxModel;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.WindowConstants;
import javax.swing.filechooser.FileFilter;

import org.alloytools.graphics.util.AlloyGraphics;

/**
 * Graphical dialog methods for asking the user some questions.
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class OurDialog {

    /**
     * The constructor is private, since this utility class never needs to be
     * instantiated.
     */
    private OurDialog() {
    }

    /**
     * Helper method for constructing an always-on-top modal dialog.
     */
    private static Object show(JFrame parent, String title, int type, Object message, Object[] options, Object initialOption) {
        if (options == null) {
            options = new Object[] {
                                    "Ok"
            };
            initialOption = "Ok";
        }
        JOptionPane p = new JOptionPane(message, type, JOptionPane.DEFAULT_OPTION, null, options, initialOption);
        p.setInitialValue(initialOption);
        JDialog d = p.createDialog(parent, title);
        p.selectInitialValue();
        d.setAlwaysOnTop(true);
        d.setVisible(true);
        d.dispose();
        return p.getValue();
    }

    /**
     * Popup the given informative message, then ask the user to click Close to
     * close it.
     */
    public static void showmsg(String title, Object... msg) {
        JButton dismiss = new JButton(Util.onMac() ? "Dismiss" : "Close");
        Object[] objs = new Object[msg.length + 1];
        System.arraycopy(msg, 0, objs, 0, msg.length);
        objs[objs.length - 1] = OurUtil.makeH(null, dismiss, null);
        JOptionPane about = new JOptionPane(objs, JOptionPane.PLAIN_MESSAGE, JOptionPane.DEFAULT_OPTION, null, new Object[] {});
        JDialog dialog = about.createDialog(null, title);
        dismiss.addActionListener(Runner.createDispose(dialog));
        dialog.setAlwaysOnTop(true);
        dialog.setVisible(true);
        dialog.dispose();
    }

    /**
     * Popup the given error message.
     */
    public static void alert(JFrame parent, Object message) {
        show(parent, "Error", ERROR_MESSAGE, message, null, null);
    }

    /**
     * Popup the given error message, then terminate the program.
     */
    public static void fatal(JFrame parent, Object message) {
        try {
            show(parent, "Fatal Error", ERROR_MESSAGE, message, null, null);
        } finally {
            System.exit(1);
        }
    }

    /**
     * Ask if the user wishes to save the file, discard the file, or cancel the
     * entire operation (default is cancel).
     *
     * @return 'c' if cancel, 's' if save, 'd' if discard
     */
    public static char askSaveDiscardCancel(JFrame parent, String description) {
        description = description + " has not been saved. Do you want to";
        Object ans = show(parent, "Warning", WARNING_MESSAGE, new String[] {
                                                                            description, "cancel the operation, close the file without saving, or save it and close?"
        }, new Object[] {
                         "Save", "Don't Save", "Cancel"
        }, "Cancel");
        return (ans == "Save") ? 's' : (ans == "Don't Save" ? 'd' : 'c');
    }

    /**
     * Ask if the user really wishes to overwrite the file (default is no).
     *
     * @return true if the user wishes to overwrite the file, false if the user does
     *         not wish to overwrite the file.
     */
    public static boolean askOverwrite(JFrame parent, String filename) {
        return "Overwrite" == show(parent, "Warning: file already exists", WARNING_MESSAGE, new String[] {
                                                                                                          "The file \"" + filename + "\"", "already exists. Do you wish to overwrite it?"
        }, new String[] {
                         "Overwrite", "Cancel"
        }, "Cancel");
    }

    /** This caches the result of the call to get all fonts. */
    private static String[] allFonts = null;

    /**
     * Returns true if a font with that name exists on the system (comparison is
     * case-insensitive).
     */
    public synchronized static boolean hasFont(String fontname) {
        // if (fontname == null) return false;
        if (allFonts == null)
            allFonts = GraphicsEnvironment.getLocalGraphicsEnvironment().getAvailableFontFamilyNames();
        if (allFonts == null)
            return false;
        for (int i = 0; i < allFonts.length; i++)
            if (fontname.compareToIgnoreCase(allFonts[i]) == 0)
                return true;
        return false;
    }

    public synchronized static String getProperFontName(String fontname, String... preferred) {
        int i = 0;
        while (true) {
            if (hasFont(fontname) || i >= preferred.length)
                return fontname;

            fontname = preferred[i++];
        }
    }

    /**
     * Asks the user to choose a font; returns "" if the user cancels the request.
     *
     */
    public static String askFont(JFrame parent) {
        JComboBox<String> wCandidates = new OurCombobox<>(new String[0]);
        JCheckBox wShowALlFonts = new JCheckBox("Show all fonts");
        JLabel sampleText = new JLabel("fun calculate[ a: X ] : Y { }");

        class Model {

            String  selected = Font.MONOSPACED;
            Boolean all      = null;

            void selected(String selected) {
                if (!Objects.equals(selected, this.selected)) {
                    this.selected = selected;
                    if (selected != null) {
                        Font font = new Font(selected, Font.PLAIN, 12);
                        sampleText.setFont(font);
                        sampleText.setBackground(Color.black);
                    } else {
                        Font font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
                        sampleText.setFont(font);
                        sampleText.setBackground(Color.red);
                    }
                }
            }

            void all(Boolean all) {
                if (!Objects.equals(this.all, all)) {
                    this.all = all;
                    String[] items = AlloyGraphics.getFontFamilyNames(all).toArray(String[]::new);
                    DefaultComboBoxModel<String> model = new DefaultComboBoxModel<>(items);
                    wCandidates.setModel(model);
                    wCandidates.setSelectedItem(selected);
                }
            }
        }
        Model model = new Model();

        wCandidates.addActionListener(event -> {
            model.selected((String) wCandidates.getSelectedItem());
        });
        wShowALlFonts.addChangeListener(event -> {
            model.all(wShowALlFonts.isSelected());
        });

        String current = A4Preferences.FontName.get();
        boolean foundInMonoFonts = AlloyGraphics.isMono(current);
        wShowALlFonts.setSelected(!foundInMonoFonts);
        model.all(!foundInMonoFonts);
        wCandidates.setSelectedItem(current);

        Object ans = show(parent, "Font", JOptionPane.INFORMATION_MESSAGE, new Object[] {
                                                                                         "Select the new font:", wCandidates, sampleText, wShowALlFonts
        }, new Object[] {
                         "Ok", "Cancel"
        }, "Ok");
        Object value = wCandidates.getSelectedItem();
        if (ans == "Ok" && (value instanceof String))
            return (String) value;
        else
            return "";
    }

    /**
     * True if we should use AWT (instead of Swing) to display the OPEN and SAVE
     * dialog.
     */
    private static boolean useAWT = Util.onMac();

    /**
     * Use the platform's preferred file chooser to ask the user to select a file.
     * <br>
     * Note: if it is a save operation, and the user didn't include an extension,
     * then we'll add the extension.
     *
     * @param parent
     * @param isOpen - true means this is an Open operation; false means this is a
     *            Save operation
     * @param dir - the initial directory (or null if we want to use the default)
     * @param ext - the file extension (including "."; using lowercase letters; for
     *            example, ".als") or ""
     * @param description - the description for the given extension
     * @return null if the user didn't choose anything, otherwise it returns the
     *         selected file
     */
    public static File askFile(Frame parent, boolean isOpen, String dir, final String ext, final String description) {
        return askFile(parent, isOpen, dir, new String[] {
                                                          ext
        }, description);
    }

    public static File askFile(Frame parent, boolean isOpen, String dir, final String exts[], final String description) {
        if (dir == null)
            dir = Util.getCurrentDirectory();
        if (!(new File(dir).isDirectory()))
            dir = System.getProperty("user.home");
        dir = Util.canon(dir);
        String ans;
        if (useAWT) {
            FileDialog open = new FileDialog(parent, isOpen ? "Open..." : "Save...");
            open.setAlwaysOnTop(true);
            open.setMode(isOpen ? FileDialog.LOAD : FileDialog.SAVE);
            open.setDirectory(dir);
            if (exts != null && exts.length > 0)
                open.setFilenameFilter(new FilenameFilter() {

                    @Override
                    public boolean accept(File dir, String name) {
                        for (String ext : exts) {
                            if (name.toLowerCase(Locale.US).endsWith(ext))
                                return true;
                        }
                        return false;
                    }
                });
            open.setVisible(true); // This method blocks until the user either
                                  // chooses something or cancels the dialog.
            open.dispose();
            if (open.getFile() == null)
                return null;
            else
                ans = open.getDirectory() + File.separatorChar + open.getFile();
        } else {
            try {
                JFileChooser open = new JFileChooser(dir) {

                    private static final long serialVersionUID = 0;

                    @Override
                    public JDialog createDialog(Component parent) throws HeadlessException {
                        JDialog dialog = super.createDialog(parent);
                        dialog.setAlwaysOnTop(true);
                        return dialog;
                    }
                };
                open.setDialogTitle(isOpen ? "Open..." : "Save...");
                open.setApproveButtonText(isOpen ? "Open" : "Save");
                open.setDialogType(isOpen ? JFileChooser.OPEN_DIALOG : JFileChooser.SAVE_DIALOG);

                if (exts != null && exts.length > 0)
                    open.setFileFilter(new FileFilter() {

                        @Override
                        public boolean accept(File file) {
                            for (String ext : exts) {
                                boolean result = !file.isFile() || file.getPath().toLowerCase(Locale.US).endsWith(ext);
                                if (result)
                                    return true;
                            }
                            return false;
                        }

                        @Override
                        public String getDescription() {
                            return description;
                        }
                    });
                if (open.showDialog(parent, null) != JFileChooser.APPROVE_OPTION || open.getSelectedFile() == null)
                    return null;
                ans = open.getSelectedFile().getPath();
            } catch (Exception ex) {
                // Some combination of Windows version and JDK version will
                // trigger this failure.
                // In such a case, we'll fall back to using the "AWT" file open
                // dialog
                useAWT = true;
                return askFile(parent, isOpen, dir, exts, description);
            }
        }
        if (!isOpen) {
            int lastSlash = ans.lastIndexOf(File.separatorChar);
            int lastDot = (lastSlash >= 0) ? ans.indexOf('.', lastSlash) : ans.indexOf('.');
            if (lastDot < 0 && exts != null && exts.length > 0)
                ans = ans + exts[0];
        }
        return new File(Util.canon(ans));
    }

    /**
     * Display "msg" in a modal dialog window, and ask the user to choose "yes"
     * versus "no" (default is "no").
     */
    public static boolean yesno(JFrame parent, Object msg, String yes, String no) {
        return show(parent, "Question", WARNING_MESSAGE, msg, new Object[] {
                                                                            yes, no
        }, no) == yes;
    }

    /**
     * Display "msg" in a modal dialog window, and ask the user to choose "Yes"
     * versus "No" (default is "no").
     */
    public static boolean yesno(JFrame parent, Object msg) {
        return yesno(parent, msg, "Yes", "No");
    }

    /**
     * Display a modal dialog window containing the "objects"; returns true iff the
     * user clicks Ok.
     */
    public static boolean getInput(JFrame parent, String title, Object... objects) {
        // If there is a JTextField or a JTextArea here, then let the first
        // JTextField or JTextArea be the initially focused widget
        Object main = "Ok";
        for (Object obj : objects)
            if (obj instanceof JTextField || obj instanceof JTextArea) {
                main = obj;
                break;
            }
        // Construct the dialog panel
        final JOptionPane pane = new JOptionPane(objects, QUESTION_MESSAGE, YES_NO_OPTION, null, new Object[] {
                                                                                                               "Ok", "Cancel"
        }, main);
        final JDialog dialog = pane.createDialog(parent, title);
        // For each JTextField and JCheckBox, add a KeyListener that detects
        // VK_ENTER and treat it as if the user clicked OK
        for (Object obj : objects)
            if (obj instanceof JTextField || obj instanceof JCheckBox) {
                ((JComponent) obj).addKeyListener(new KeyListener() {

                    @Override
                    public void keyPressed(KeyEvent e) {
                        if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                            pane.setValue("Ok");
                            dialog.dispose();
                        }
                    }

                    @Override
                    public void keyReleased(KeyEvent e) {
                    }

                    @Override
                    public void keyTyped(KeyEvent e) {
                    }
                });
            }
        dialog.setAlwaysOnTop(true);
        dialog.setVisible(true); // This method blocks until the user either
                                // chooses something or cancels the dialog.
        dialog.dispose();
        return pane.getValue() == "Ok";
    }

    /** Display a simple non-modal window showing some text. */
    public static JFrame showtext(String title, String text) {
        JFrame window = new JFrame(title);
        JButton done = new JButton("Close");
        done.addActionListener(Runner.createDispose(window));
        JScrollPane scrollPane = OurUtil.scrollpane(OurUtil.textarea(text, 40, 90, false, false));
        window.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        window.getContentPane().setLayout(new BorderLayout());
        window.getContentPane().add(scrollPane, BorderLayout.CENTER);
        window.getContentPane().add(done, BorderLayout.SOUTH);
        window.pack();
        window.setSize(500, 500);
        window.setLocationRelativeTo(null);
        window.setVisible(true);
        return window;
    }
}
