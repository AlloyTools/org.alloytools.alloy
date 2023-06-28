package edu.mit.csail.sdg.alloy4whole;


import static javax.swing.KeyStroke.getKeyStroke;

import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.InputMap;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
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


    static class ReverseString implements CharSequence {

        final CharSequence source;
        final int          start;
        final int          end;

        public ReverseString(CharSequence source, int start, int end) {
            this.source = source;
            this.start = start;
            this.end = end;
        }

        public ReverseString(CharSequence source) {
            this.source = source;
            this.start = 0;
            this.end = source.length();
        }

        @Override
        public int length() {
            return this.end - this.start;
        }

        @Override
        public char charAt(int index) {
            return source.charAt(translate(index));
        }

        @Override
        public CharSequence subSequence(int start, int end) {
            return new ReverseString(source, translate(end) + 1, translate(start) + 1);
        }

        public int translate(int n) {
            return this.end - 1 - n;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder(source.subSequence(start, end));
            sb.reverse();
            return sb.toString();
        }
    }

    static class Search {

        final JTextPane source;
        final boolean   reverse;
        public int      start;
        public int      end;

        Search(JTextPane source, int start, int end, boolean reverse) {
            this.source = source;
            this.start = start;
            this.end = end;
            this.reverse = reverse;
        }

        public Point find(Pattern pattern) {

            String text = source.getText();
            if (end < 0)
                end = text.length();

            CharSequence domain = reverse ? new ReverseString(text, start, end) : text.subSequence(start, end);

            Matcher matcher = pattern.matcher(domain);
            if (matcher.find()) {

                int xstart = matcher.start() + start;
                int xend = matcher.end() + start;
                if (reverse) {
                    xstart = end - matcher.end();
                    xend = end - matcher.start();
                }
                return new Point(xstart, xend);
            }
            return null;
        }

    }

    public class FindReplaceDialog extends JDialog {

        private static final long serialVersionUID = 1L;
        final JTextField          findField;
        final JTextField          replaceField;
        final JCheckBox           smartCaseCheckBox;
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
        final JCheckBox           backwardCheckBox;

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

            smartCaseCheckBox = new JCheckBox("Smart Case");
            constraints.gridx = 0;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(smartCaseCheckBox, constraints);

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

            allPanesCheckBox = new JCheckBox("All tabs");
            constraints.gridx = 3;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(allPanesCheckBox, constraints);

            backwardCheckBox = new JCheckBox("Backward");
            constraints.gridx = 4;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(backwardCheckBox, constraints);

            row++;

            findButton = new JButton("Find");
            constraints.gridx = 0;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(findButton, constraints);

            replaceFindButton = new JButton("Replace>Find");
            constraints.gridx = 1;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(replaceFindButton, constraints);

            replaceButton = new JButton("Replace");
            constraints.gridx = 2;
            constraints.gridy = row;
            constraints.gridwidth = 1;
            panel.add(replaceButton, constraints);

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
            smartCaseCheckBox.setSelected(true);

            findField.addActionListener(e -> find());
            replaceField.addActionListener(e -> {
                if (find())
                    replace();
            });

            findButton.addActionListener(e -> find());
            replaceButton.addActionListener(e -> replace());
            replaceFindButton.addActionListener(e -> replaceFind());
            replaceAllButton.addActionListener(e -> replaceAll());
            closeButton.addActionListener(e -> {
                FindReplaceDialog.this.setVisible(false);
                active = false;
            });

            int modifier = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();

            InputMap inputMap = panel.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
            inputMap.put(getKeyStroke(KeyEvent.VK_F, modifier), "find");
            inputMap.put(getKeyStroke(KeyEvent.VK_F, KeyEvent.SHIFT_DOWN_MASK + modifier), "find.reversed");
            inputMap.put(getKeyStroke(KeyEvent.VK_G, modifier), "find");
            inputMap.put(getKeyStroke(KeyEvent.VK_G, KeyEvent.SHIFT_DOWN_MASK + modifier), "find.reversed");

            panel.getActionMap().put("find", make(e -> find()));
            panel.getActionMap().put("find.reversed", make(e -> find(true)));

            setTitle("Find/Replace Text");
            setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
            pack();
            setAlwaysOnTop(false);
        }

        boolean find() {
            return find(backwardCheckBox.isSelected());
        }

        boolean find(boolean reversed) {
            messageField.setText("");
            CharSequence findText = findField.getText();
            JTextPane firstPane = pane.apply(0).orElse(null);

            List<Search> l = new ArrayList<>();
            l.add(new Search(firstPane, firstPane.getSelectionEnd(), -1, reversed));
            if (allPanesCheckBox.isSelected()) {
                int tab = 1;
                while (true) {
                    JTextPane textPane = pane.apply(tab).orElse(null);
                    if (textPane == null)
                        break;
                    l.add(new Search(textPane, 0, -1, reversed));
                    tab++;
                }
            }
            l.add(new Search(firstPane, 0, reversed ? firstPane.getSelectionStart() : -1, reversed));
            if (reversed) {
                Collections.reverse(l);
                findText = new ReverseString(findText);
            }

            Pattern pattern = getPattern(findText);

            for (Search search : l) {
                Point d;
                if ((d = search.find(pattern)) != null) {
                    JTextPane pane = search.source;
                    foundMatch(pane, d.x, d.y);
                    return true;
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
            select.accept(textPane);
            replaceButton.setEnabled(true);
            replaceAllButton.setEnabled(true);
            replaceFindButton.setEnabled(true);
            return true;
        }

        private Pattern getPattern(CharSequence target) {
            String glob;
            int flags = Pattern.MULTILINE;
            if (smartCaseCheckBox.isSelected() && allLowerCase(target)) {
                flags |= Pattern.CASE_INSENSITIVE;
            }
            if (wholeWordCheckBox.isSelected()) {
                target = "\\b" + target + "\\b";
            }
            glob = Glob.toPattern(target.toString(), flags).toString();


            String RELUCTANT_WILDCARD = ".*?";
            glob = glob.replaceAll("(?<!\\\\)\\.\\*", RELUCTANT_WILDCARD);
            System.out.println(glob);
            return Pattern.compile(glob, flags);
        }

        private boolean allLowerCase(CharSequence target) {
            for (int i = 0; i < target.length(); i++) {
                if (Character.isUpperCase(target.charAt(i))) {
                    return false;
                }
            }
            return true;
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
                Matcher m = getPattern(findText).matcher(selectedText);
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
                Matcher m = getPattern(findText).matcher(currentText);
                StringBuffer sb = new StringBuffer();
                while (m.find()) {
                    m.appendReplacement(sb, replace(m, replaceText));
                    occurrences++;
                }
                m.appendTail(sb);

                textPane.setText(sb.toString());

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

    private Action make(Consumer<ActionEvent> action) {
        return new AbstractAction() {

            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                action.accept(e);
            }
        };
    }

}
