package edu.mit.csail.sdg.alloy4whole;


import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.JTextPane;

import aQute.libg.glob.Glob;

/**
 * Handles the logic & UI to search and replace on a JTextPane
 */
public class FindReplace {

    final JFrame                                frame;
    final Function<Integer,Optional<JTextPane>> pane;
    final Consumer<JTextPane>                   select;
    final FindReplaceDialog                     dialog;

    String                                      find          = "";
    String                                      replace       = "";
    boolean                                     caseSensitive = false;
    boolean                                     wholeWord     = false;
    boolean                                     active;


    public class FindReplaceDialog extends JDialog {

        private static final long serialVersionUID = 1L;
        final JTextField          findField;
        final JTextField          replaceField;
        final JCheckBox           caseSensitiveCheckBox;
        final JCheckBox           wrapSearchCheckBox;
        final JCheckBox           wholeWordCheckBox;
        final JCheckBox           allPanesCheckBox;
        final JButton             findButton;
        final JButton             replaceButton;
        final JButton             replaceAllButton;
        final JButton             closeButton;
        final JPanel              panel;
        final JLabel              messageField;
        final JButton             replaceFindButton;

        FindReplaceDialog(Window window) {
            super(window);
            panel = new JPanel(new GridBagLayout());
            this.add(panel);
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.fill = GridBagConstraints.HORIZONTAL;
            constraints.anchor = GridBagConstraints.WEST;
            constraints.insets = new Insets(5, 5, 5, 5);
            constraints.weightx = 1;

            int columns = 5;
            int row = 0;

            JLabel findLabel = new JLabel("Find:");
            constraints.gridx = 0;
            constraints.gridy = row;
            panel.add(findLabel, constraints);

            findField = new JTextField(20);
            constraints.gridx = 1;
            constraints.gridy = row;
            constraints.gridwidth = columns - 1;
            panel.add(findField, constraints);

            row++;

            JLabel replaceLabel = new JLabel("Replace:");
            constraints.gridx = 0;
            constraints.gridy = row;
            panel.add(replaceLabel, constraints);

            replaceField = new JTextField(20);
            constraints.gridx = 1;
            constraints.gridy = row;
            constraints.gridwidth = columns - 1;
            panel.add(replaceField, constraints);

            row++;

            caseSensitiveCheckBox = new JCheckBox("Case Sensitive");
            constraints.gridx = 0;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(caseSensitiveCheckBox, constraints);

            wrapSearchCheckBox = new JCheckBox("Wrap Search");
            constraints.gridx = 1;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(wrapSearchCheckBox, constraints);

            wholeWordCheckBox = new JCheckBox("Whole Word");
            constraints.gridx = 2;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(wholeWordCheckBox, constraints);

            allPanesCheckBox = new JCheckBox("Search tabs");
            constraints.gridx = 3;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(allPanesCheckBox, constraints);

            row++;

            findButton = new JButton("Find");
            constraints.gridx = 0;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(findButton, constraints);

            replaceButton = new JButton("Replace");
            constraints.gridx = 1;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(replaceButton, constraints);

            replaceFindButton = new JButton("Replace>Find");
            constraints.gridx = 2;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(replaceFindButton, constraints);

            replaceAllButton = new JButton("Replace All");
            constraints.gridx = 3;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(replaceAllButton, constraints);

            closeButton = new JButton("Close");
            constraints.gridx = 4;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(closeButton, constraints);

            row++;

            messageField = new JLabel();
            messageField.setText(" ");
            constraints.gridx = 0;
            constraints.gridy = row;
            constraints.gridwidth = 4;
            constraints.gridheight = 2;
            panel.add(messageField, constraints);

            findButton.setEnabled(true);
            replaceFindButton.setEnabled(false);
            replaceButton.setEnabled(false);
            replaceAllButton.setEnabled(false);

            wrapSearchCheckBox.setSelected(true);
            caseSensitiveCheckBox.setSelected(true);

            findButton.addActionListener(new ActionListener() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    find();
                }
            });

            replaceButton.addActionListener(new ActionListener() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    replace();
                }
            });

            replaceFindButton.addActionListener(new ActionListener() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    replaceFind();
                }
            });

            replaceAllButton.addActionListener(new ActionListener() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    replaceAll();
                }
            });

            closeButton.addActionListener(new ActionListener() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    FindReplaceDialog.this.setVisible(false);
                    save();
                    active = false;
                }
            });

            setTitle("Find/Replace Text");
            setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
            pack();
            setAlwaysOnTop(false);
        }

        boolean find() {
            messageField.setText("");
            int tab = 0;
            JTextPane textPane = pane.apply(0).orElse(null);
            String findText = findField.getText();
            String currentText = textPane.getText();
            int startIndex = textPane.getSelectionEnd();

            do {
                Matcher m = getMatcher(findText, currentText.substring(startIndex));
                if (m.find()) {
                    int start = m.start() + startIndex, end = m.end() + startIndex;
                    return foundMatch(textPane, start, end);
                }
                startIndex = 0;
                textPane = pane.apply(++tab).orElse(null);
            }
            while (allPanesCheckBox.isSelected() && textPane != null);

            if (wrapSearchCheckBox.isSelected()) {
                textPane = pane.apply(0).orElse(null);
                Matcher m = getMatcher(findText, currentText.substring(0, textPane.getSelectionEnd()));
                if (m.find(0)) {
                    return foundMatch(textPane, m.start(), m.end());
                }
            }
            return missedMatch("Reached end of text, text not found");
        }

        private boolean missedMatch(String message) {
            replaceButton.setEnabled(false);
            replaceAllButton.setEnabled(false);
            replaceFindButton.setEnabled(false);
            Toolkit.getDefaultToolkit().beep();
            messageField.setText(message);
            return false;

        }

        private boolean foundMatch(JTextPane textPane, int start, int end) {
            textPane.setSelectionStart(start);
            textPane.setSelectionEnd(end);
            replaceButton.setEnabled(true);
            replaceAllButton.setEnabled(true);
            replaceFindButton.setEnabled(true);
            select.accept(textPane);
            return true;
        }

        private Matcher getMatcher(String target, String source) {
            String glob;
            int flags = Pattern.MULTILINE;
            if (caseSensitiveCheckBox.isSelected()) {
                flags |= Pattern.CASE_INSENSITIVE;
            }
            if (wholeWordCheckBox.isSelected()) {
                target = "\\b" + target + "\\b";
            }
            glob = Glob.toPattern(target, flags).toString();


            String RELUCTANT_WILDCARD = ".*?";
            glob = glob.replaceAll("(?<!\\\\)\\.\\*", RELUCTANT_WILDCARD);
            System.out.println(glob);
            return Pattern.compile(glob, flags).matcher(source);
        }

        private boolean replace() {
            JTextPane textPane = pane.apply(0).orElseThrow(() -> new IllegalStateException("Should always have at least one pane"));
            String findText = findField.getText();
            String replaceText = replaceField.getText();
            String currentText = textPane.getText();
            int startIndex = textPane.getSelectionStart();
            int endIndex = textPane.getSelectionEnd();
            if (startIndex != endIndex) {
                String selectedText = currentText.substring(startIndex, endIndex);
                Matcher m = getMatcher(findText, selectedText);
                if (m.lookingAt()) {
                    textPane.replaceSelection(replace(m, replaceText));
                    return true;
                } else {
                    Toolkit.getDefaultToolkit().beep();
                    messageField.setText("Selected text does not match the text to find.");
                }
            } else {
                Toolkit.getDefaultToolkit().beep();
                messageField.setText("No text selected.");
            }
            return false;
        }

        private void replaceFind() {
            if (replace())
                find();
        }

        private void replaceAll() {
            int tab = 0;
            int occurrences = 0;
            JTextPane textPane = getPane(tab);
            do {
                String findText = findField.getText();
                String replaceText = replaceField.getText();
                String currentText = textPane.getText();
                Matcher m = getMatcher(findText, currentText);
                StringBuffer sb = new StringBuffer();
                while (m.find()) {
                    m.appendReplacement(sb, replace(m, replaceText));
                    occurrences++;
                }
                m.appendTail(sb);

                textPane.setText(sb.toString());
                if (!allPanesCheckBox.isSelected())
                    break;

                tab++;
                textPane = getPane(tab);
            }
            while (allPanesCheckBox.isSelected() && textPane != null);

            messageField.setText("Replaced " + occurrences + " occurrences in " + tab + " tabs");
        }

        private JTextPane getPane(int tab) {
            return pane.apply(tab).orElse(null);
        }

        private String replace(Matcher m, String replaceText) {
            StringBuffer sb = new StringBuffer(replaceText);
            for (int i = 0; i < sb.length() - 1; i++) {
                char c = sb.charAt(i);
                if (c == '\\' && sb.charAt(i + 1) == '$')
                    i += 2;
                else if (c == '$' && Character.isDigit(sb.charAt(i + 1))) {
                    int index = sb.charAt(i + 1) - '0';
                    if (m.groupCount() >= index) {
                        sb.delete(i, i + 2);

                        String group = m.group(index);
                        if (group != null) {
                            sb.insert(i, group);
                            i += group.length() - 1;
                        }
                    }
                }
            }
            return sb.toString();
        }

        void load() {
            caseSensitiveCheckBox.setSelected(caseSensitive);
            findField.setText(find);
            replaceField.setText(replace);
        }

        void save() {
            caseSensitive = caseSensitiveCheckBox.isSelected();
            find = findField.getText();
            replace = replaceField.getText();
        }

    }

    public FindReplace(JFrame frame, Function<Integer,Optional<JTextPane>> currentPane, Consumer<JTextPane> select) {
        this.frame = frame;
        this.pane = currentPane;
        this.select = select;
        this.dialog = new FindReplaceDialog(frame);
    }

    public void find() {
        JTextPane textPane = pane.apply(0).get();
        String selectedText = textPane.getSelectedText();
        if (selectedText != null) {
            dialog.findField.setText(selectedText);
        }
        active = true;
        int x = frame.getX() + (frame.getWidth() - dialog.getWidth()) / 2;
        int y = frame.getY() + (frame.getHeight() - dialog.getHeight()) / 2;
        dialog.setLocation(x, y);
        dialog.setVisible(true);
    }

    public void findNext() {
        dialog.find();
    }
}
