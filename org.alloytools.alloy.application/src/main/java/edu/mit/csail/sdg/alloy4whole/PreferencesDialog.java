package edu.mit.csail.sdg.alloy4whole;

import static edu.mit.csail.sdg.alloy4.A4Preferences.AntiAlias;
import static edu.mit.csail.sdg.alloy4.A4Preferences.AutoVisualize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreGranularity;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreMinimization;
import static edu.mit.csail.sdg.alloy4.A4Preferences.DecomposePref;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontName;
import static edu.mit.csail.sdg.alloy4.A4Preferences.FontSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.ImplicitThis;
import static edu.mit.csail.sdg.alloy4.A4Preferences.InferPartialInstance;
import static edu.mit.csail.sdg.alloy4.A4Preferences.LAF;
import static edu.mit.csail.sdg.alloy4.A4Preferences.NoOverflow;
import static edu.mit.csail.sdg.alloy4.A4Preferences.RecordKodkod;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SkolemDepth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Solver;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubMemory;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SubStack;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SyntaxDisabled;
import static edu.mit.csail.sdg.alloy4.A4Preferences.TabSize;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Unrolls;
import static edu.mit.csail.sdg.alloy4.A4Preferences.VerbosityPref;
import static edu.mit.csail.sdg.alloy4.A4Preferences.WarningNonfatal;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Welcome;

import java.awt.Component;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import javax.swing.AbstractAction;
import javax.swing.AbstractListModel;
import javax.swing.AbstractSpinnerModel;
import javax.swing.Action;
import javax.swing.BoundedRangeModel;
import javax.swing.ComboBoxModel;
import javax.swing.Icon;
import javax.swing.InputVerifier;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.JSpinner;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.SpinnerModel;
import javax.swing.SwingUtilities;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.plaf.basic.BasicComboBoxRenderer;

import edu.mit.csail.sdg.alloy4.A4Preferences.BooleanPref;
import edu.mit.csail.sdg.alloy4.A4Preferences.ChoicePref;
import edu.mit.csail.sdg.alloy4.A4Preferences.IntPref;
import edu.mit.csail.sdg.alloy4.A4Preferences.Pref;
import edu.mit.csail.sdg.alloy4.OurBorder;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.OurUtil.GridBagConstraintsBuilder;
import edu.mit.csail.sdg.alloy4.Subprocess;
import edu.mit.csail.sdg.translator.A4Options.SatSolver;

/**
 * @modified [electrum] only log when debugging; load electrod binary
 *           executables; added decompose strategy option
 */
@SuppressWarnings({
                   "serial"
} )
public class PreferencesDialog extends JFrame {

    private static final long serialVersionUID = 5577892964740788892L;
    private JTabbedPane       tab;
    // private JPanel editorPane;
    // private JPanel solverPane;
    // private JPanel miscPane;

    final static boolean isDebug = "yes".equals(System.getProperty("debug"));

    private static class MyIntSpinnerModel extends AbstractSpinnerModel {

        private final IntPref pref;

        public MyIntSpinnerModel(final IntPref pref) {
            this.pref = pref;
            this.pref.addChangeListener(new ChangeListener() {

                @Override
                public void stateChanged(ChangeEvent e) {
                    fireStateChanged();
                }
            });
        }

        @Override
        public Object getValue() {
            return pref.get();
        }

        @Override
        public void setValue(Object value) {
            pref.set((Integer) value);
        }

        @Override
        public Object getNextValue() {
            return Math.min(pref.max, pref.get() + 1);
        }

        @Override
        public Object getPreviousValue() {
            return Math.max(pref.min, pref.get() - 1);
        }
    }

    @SuppressWarnings("unchecked" )
    private static class CBModel<T> extends AbstractListModel implements ComboBoxModel {

        private final ChoicePref<T> pref;

        public CBModel(final ChoicePref<T> pref) {
            this.pref = pref;
            this.pref.addChangeListener(new ChangeListener() {

                @Override
                public void stateChanged(ChangeEvent e) {
                    fireContentsChanged(pref, -1, -1);
                }
            });
        }

        @Override
        public int getSize() {
            return pref.validChoices().size();
        }

        @Override
        public Object getElementAt(int index) {
            return pref.validChoices().get(index);
        }

        @Override
        public void setSelectedItem(Object anItem) {
            pref.set((T) anItem);
        }

        @Override
        public Object getSelectedItem() {
            return pref.get();
        }
    }

    private static class BRModel<T> implements BoundedRangeModel {

        private final ChoicePref<T> pref;

        public BRModel(ChoicePref<T> pref) {
            this.pref = pref;
        }

        @Override
        public int getMinimum() {
            return 0;
        }

        @Override
        public int getMaximum() {
            return pref.validChoices().size() - 1;
        }

        @Override
        public int getValue() {
            return pref.getSelectedIndex();
        }

        @Override
        public int getExtent() {
            return 0;
        }

        @Override
        public void setValueIsAdjusting(boolean b) {}

        @Override
        public boolean getValueIsAdjusting() {
            return false;
        }

        @Override
        public void setRangeProperties(int value, int extent, int min, int max, boolean adjusting) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void addChangeListener(ChangeListener x) {
            pref.addChangeListener(x);
        }

        @Override
        public void removeChangeListener(ChangeListener x) {
            pref.removeChangeListener(x);
        }

        @Override
        public void setValue(int n) {
            if (n >= getMinimum() && n <= getMaximum())
                pref.setSelectedIndex(n);
        }

        @Override
        public void setExtent(int n) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void setMinimum(int n) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void setMaximum(int n) {
            throw new UnsupportedOperationException();
        }
    }

    private abstract class CBRenderer extends BasicComboBoxRenderer {

        @Override
        public Component getListCellRendererComponent(JList list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
            return super.getListCellRendererComponent(list, render(value), index, isSelected, cellHasFocus);
        }

        protected abstract Object render(Object value);
    }

    private final Map<Pref< ? >,JComponent> pref2comp = new HashMap<Pref< ? >,JComponent>();
    private final String                    binary;
    private final SwingLogPanel             log;

    public PreferencesDialog(SwingLogPanel log, String binary) {
        this.log = log;
        this.binary = binary;
        if (log != null && binary != null) {
            Solver.setChoices(testSolvers(), SatSolver.SAT4J);
        }
        initUI();
    }

    protected Iterable<SatSolver> testSolvers() {
        List<SatSolver> satChoices = SatSolver.values().makeCopy();
        satChoices.remove(SatSolver.BerkMinPIPE);
        String fs = System.getProperty("file.separator");
        String test2 = Subprocess.exec(20000, new String[] {
                                                            binary + fs + "spear", "--model", "--dimacs", binary + fs + "tmp.cnf"
        });
        if (!isSat(test2))
            satChoices.remove(SatSolver.SpearPIPE);
        if (!loadLibrary("minisat")) {
            log.logBold("Warning: JNI-based SAT solver does not work on this platform.\n");
            log.log("This is okay, since you can still use SAT4J as the solver.\n" + "For more information, please visit http://alloy.mit.edu/alloy4/\n");
            log.logDivider();
            log.flush();
            satChoices.remove(SatSolver.MiniSatJNI);
        }
        if (!loadLibrary("minisatprover"))
            satChoices.remove(SatSolver.MiniSatProverJNI);
        if (!loadLibrary("lingeling"))
            satChoices.remove(SatSolver.LingelingJNI);
        if (!loadLibrary("glucose"))
            satChoices.remove(SatSolver.GlucoseJNI);
        if (!loadLibrary("cryptominisat"))
            satChoices.remove(SatSolver.CryptoMiniSatJNI);
        // [electrum] load unbounded model checking backend
        if (!staticLibrary("electrod")) {
            satChoices.remove(SatSolver.ElectrodX);
            satChoices.remove(SatSolver.ElectrodS);
        }
        if (!staticLibrary("NuSMV"))
            satChoices.remove(SatSolver.ElectrodS);
        if (!staticLibrary("nuXmv"))
            satChoices.remove(SatSolver.ElectrodX);
        SatSolver now = Solver.get();
        if (!satChoices.contains(now)) {
            now = SatSolver.LingelingJNI;
            if (!satChoices.contains(now))
                now = SatSolver.SAT4J;
            Solver.set(now);
        }
        if (now == SatSolver.SAT4J && satChoices.size() > 3 && satChoices.contains(SatSolver.CNF) && satChoices.contains(SatSolver.KK)) {
            log.logBold("Warning: Alloy4 defaults to SAT4J since it is pure Java and very reliable.\n");
            log.log("For faster performance, go to Options menu and try another solver like MiniSat.\n");
            log.log("If these native solvers fail on your computer, remember to change back to SAT4J.\n");
            log.logDivider();
            log.flush();
        }
        return satChoices;
    }

    /**
     * Returns true iff the output says "s SATISFIABLE" (while ignoring comment
     * lines and value lines)
     */
    private static boolean isSat(String output) {
        int i = 0, n = output.length();
        // skip COMMENT lines and VALUE lines
        while (i < n && (output.charAt(i) == 'c' || output.charAt(i) == 'v')) {
            while (i < n && (output.charAt(i) != '\r' && output.charAt(i) != '\n'))
                i++;
            while (i < n && (output.charAt(i) == '\r' || output.charAt(i) == '\n'))
                i++;
            continue;
        }
        return output.substring(i).startsWith("s SATISFIABLE");
    }

    private static boolean staticLibrary(String name) {
        // check if in java library path
        final String[] dirs = System.getProperty("java.library.path").split(System.getProperty("path.separator"));
        for (int i = dirs.length - 1; i >= 0; i--) {
            final File file = new File(dirs[i] + File.separator + name);
            if (file.canExecute()) {
                if (isDebug)
                    System.out.println("Loaded: " + name + " at " + file);
                return true;
            }
        }
        // check if in system path
        for (String str : (System.getenv("PATH")).split(Pattern.quote(File.pathSeparator))) {
            Path pth = Paths.get(str);
            if (Files.exists(pth.resolve(name))) {
                if (isDebug)
                    System.out.println("Loaded: " + name + " at " + pth);
                return true;
            }
        }

        if (isDebug)
            System.out.println("Failed to load: " + name);
        return false;
    }


    private boolean loadLibrary(String library) {
        boolean loaded = _loadLibrary(library);
        if (isDebug)
            if (loaded)
                System.out.println("Loaded: " + library);
            else
                System.out.println("Failed to load: " + library);
        return loaded;
    }

    private static boolean _loadLibrary(String library) {
        try {
            System.loadLibrary(library);
            return true;
        } catch (UnsatisfiedLinkError ex) {
        }
        try {
            System.loadLibrary(library + "x1");
            return true;
        } catch (UnsatisfiedLinkError ex) {}
        try {
            System.loadLibrary(library + "x2");
            return true;
        } catch (UnsatisfiedLinkError ex) {}
        try {
            System.loadLibrary(library + "x3");
            return true;
        } catch (UnsatisfiedLinkError ex) {}
        try {
            System.loadLibrary(library + "x4");
            return true;
        } catch (UnsatisfiedLinkError ex) {}
        try {
            System.loadLibrary(library + "x5");
            return true;
        } catch (UnsatisfiedLinkError ex) {
            return false;
        }
    }

    protected final void initUI() {
        this.tab = new JTabbedPane();

        tab.addTab("Editor", initEditorPane());
        tab.addTab("Solver", initSolverPane());
        tab.addTab("Miscellaneous", initMiscPane());

        add(tab);
        setTitle("Alloy Preferences");
        pack();
        setSize(getSize().width + 5, getSize().height + 5);
        setResizable(false);
        setLocationRelativeTo(null);
        setAlwaysOnTop(true);
    }

    protected Component initEditorPane() {
        JPanel p = OurUtil.makeGrid(2, gbc().make(), mkCombo(FontName), mkCombo(FontSize), mkCombo(TabSize));
        addToGrid(p, mkCheckBox(SyntaxDisabled), gbc().pos(0, 3).gridwidth(2));
        addToGrid(p, mkCheckBox(AntiAlias), gbc().pos(0, 4).gridwidth(2));

        // JPanel p = new JPanel(new GridBagLayout());
        // addToGrid(p, mkCheckBox(SyntaxDisabled), gbc().pos(0,
        // 0).gridwidth(2));
        // addToGrid(p, mkCheckBox(AntiAlias), gbc().pos(0, 1).gridwidth(2));
        // addRowToGrid(p, gbc().pos(0, 2), mkComboArr(FontName));
        // addRowToGrid(p, gbc().pos(0, 3), mkComboArr(FontSize));
        // addRowToGrid(p, gbc().pos(0, 4), mkComboArr(TabSize));

        return makeTabPane(p);
    }

    protected Component initSolverPane() {
        JPanel p = OurUtil.makeGrid(2, gbc().make(), mkCombo(Solver), mkSlider(SkolemDepth), mkCombo(Unrolls), mkCombo(CoreGranularity), mkSlider(CoreMinimization), mkSlider(DecomposePref));
        int r = 6;
        addToGrid(p, mkCheckBox(NoOverflow), gbc().pos(0, r++).gridwidth(2));
        addToGrid(p, mkCheckBox(ImplicitThis), gbc().pos(0, r++).gridwidth(2));
        addToGrid(p, mkCheckBox(InferPartialInstance), gbc().pos(0, r++).gridwidth(2));
        addToGrid(p, mkCheckBox(RecordKodkod), gbc().pos(0, r++).gridwidth(2));

        Solver.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                boolean enableCore = Solver.get() == SatSolver.MiniSatProverJNI;
                pref2comp.get(CoreGranularity).setEnabled(enableCore);
                pref2comp.get(CoreMinimization).setEnabled(enableCore);
            }
        });

        return makeTabPane(p);
    }

    protected Component initMiscPane() {
        JPanel p = OurUtil.makeGrid(2, gbc().make(), mkCombo(SubMemory), mkCombo(SubStack), mkCombo(VerbosityPref), mkCombo(LAF));
        int r = 4;
        addToGrid(p, mkCheckBox(Welcome), gbc().pos(0, r++).gridwidth(2));
        addToGrid(p, mkCheckBox(WarningNonfatal), gbc().pos(0, r++).gridwidth(2));
        addToGrid(p, mkCheckBox(AutoVisualize), gbc().pos(0, r++).gridwidth(2));
        return makeTabPane(p);
    }

    protected JCheckBox mkCheckBox(final BooleanPref pref) {
        final JCheckBox cb = make(new JCheckBox(pref.getTitleAction()));
        pref2comp.put(pref, cb);
        ChangeListener ctrl = new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                cb.setSelected(pref.get());
            }
        };
        pref.addChangeListener(ctrl);
        ctrl.stateChanged(null);
        return cb;
    }

    protected <T> JPanel mkSlider(final ChoicePref<T> pref) {
        final JSlider sl = make(new JSlider(mkBoundedRangeModel(pref)));
        pref2comp.put(pref, sl);
        sl.setMajorTickSpacing(1);
        sl.setMinorTickSpacing(1);
        sl.setPaintTicks(true);
        sl.setPaintLabels(true);
        sl.setSnapToTicks(true);
        sl.setLabelTable(mkDict(pref));
        pref.addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                sl.setLabelTable(mkDict(pref));
            }
        });
        sl.addMouseListener(new MouseAdapter() {

            @Override
            public void mouseReleased(MouseEvent e) {
                SwingUtilities.invokeLater(new Runnable() {

                    @Override
                    public void run() {
                        sl.updateUI();
                    }
                });
            }
        });
        return OurUtil.makeH(pref.title + ": ", sl);
    }

    private <T> Hashtable<Integer,JLabel> mkDict(final ChoicePref<T> pref) {
        Hashtable<Integer,JLabel> dict = new Hashtable<Integer,JLabel>();
        int sel = pref.getSelectedIndex();
        for (int i = 0; i < pref.validChoices().size(); i++) {
            JLabel label = makeLabel(pref.renderValueShort(pref.validChoices().get(i)));
            if (i == sel) {
                Font font = label.getFont();
                label = OurUtil.make(label, new Font(font.getName(), Font.BOLD, font.getSize()));
            }
            dict.put(i, label);
        }
        return dict;
    }

    protected JPanel mkSpinner(final IntPref pref) {
        JSpinner jsp = new JSpinner(mkSpinnerModelFor(pref));
        return OurUtil.makeH(pref.title + ": ", jsp);
    }

    protected JPanel mkEditor(final IntPref pref) {
        final JTextField jtf = new JTextField(pref.get().toString());
        jtf.setInputVerifier(new InputVerifier() {

            @Override
            public boolean verify(JComponent input) {
                try {
                    JTextField src = (JTextField) input;
                    Integer.parseInt(src.getText());
                    return true;
                } catch (NumberFormatException e) {
                    return false;
                }
            }
        });
        jtf.addKeyListener(new KeyAdapter() {

            @Override
            public void keyTyped(KeyEvent e) {
                char c = e.getKeyChar();
                if (c < '0' || c > '9') {
                    e.consume(); // ignore event
                }
            }
        });
        jtf.getDocument().addDocumentListener(new DocumentListener() {

            @Override
            public void removeUpdate(DocumentEvent e) {
                updatePref();
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                updatePref();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                updatePref();
            }

            private void updatePref() {
                String val = jtf.getText();
                try {
                    pref.set(Integer.parseInt(val));
                } catch (NumberFormatException ex) {}
            }
        });
        return OurUtil.makeH(pref.title + ": ", jtf);
    }

    @SuppressWarnings({
                       "unchecked"
    } )
    protected <T> JPanel mkCombo(final ChoicePref<T> pref) {
        JComboBox cb = make(new JComboBox(mkComboBoxModelFor(pref)));
        pref2comp.put(pref, cb);
        cb.setRenderer(new CBRenderer() {

            @Override
            protected Object render(Object value) {
                return pref.renderValueShort((T) value);
            }
        });
        return OurUtil.makeH(pref.title + ": ", cb);
    }

    protected <T> Component[] mkComboArr(final ChoicePref<T> pref) {
        return mkCombo(pref).getComponents();
    }

    private SpinnerModel mkSpinnerModelFor(IntPref pref) {
        return new MyIntSpinnerModel(pref);
    }

    private <T> ComboBoxModel mkComboBoxModelFor(ChoicePref<T> pref) {
        return new CBModel<T>(pref);
    }

    private <T> BoundedRangeModel mkBoundedRangeModel(ChoicePref<T> pref) {
        return new BRModel<T>(pref);
    }

    private <T extends JComponent> T make(T comp) {
        return OurUtil.make(comp);
    }

    private JLabel makeLabel(Object obj) {
        return OurUtil.make(new JLabel(obj.toString()));
    }

    private Component makeTabPane(JPanel pane) {
        JPanel p = new JPanel(new GridBagLayout());
        // pane.setBorder(new OurBorder(true, true, true, true));
        p.add(pane, gbc().pos(0, 0).fill(GridBagConstraints.BOTH).insets(new Insets(5, 5, 5, 5)).anchor(GridBagConstraints.NORTH).make());
        p.add(new JLabel(), gbc().pos(0, 1).weighty(1).fill(GridBagConstraints.BOTH).make());
        JPanel ans = OurUtil.make(p, new OurBorder(true, true, true, true));
        return ans;
    }

    // private void addRowToGrid(JPanel p, GridBagConstraintsBuilder builder,
    // Component[] comps) {
    // GridBagConstraints cstr = builder.make();
    // for (int i = 0; i < comps.length; i++) {
    // GridBagConstraints x = (GridBagConstraints) cstr.clone();
    // x.gridx = i;
    // p.add(comps[i], x);
    // }
    // }

    private void addToGrid(JPanel p, Component c, GridBagConstraintsBuilder cstr) {
        p.add(c, cstr.make());
    }

    private GridBagConstraintsBuilder gbc() {
        GridBagConstraintsBuilder ans = new GridBagConstraintsBuilder();
        ans.anchor(GridBagConstraints.WEST).insets(new Insets(3, 3, 3, 3)).ipads(3, 3).fill(GridBagConstraints.BOTH);
        return ans;
    }

    public void addChangeListener(ChangeListener l, Pref< ? >... prefs) {
        for (Pref< ? > pref : prefs) {
            pref.addChangeListener(l);
        }
    }

    public static Action decorateWithLogging(final SwingLogPanel log, final Pref< ? > pref, final Action action) {
        if (log == null)
            return action;
        return new AbstractAction((String) action.getValue(Action.NAME), (Icon) action.getValue(Action.SMALL_ICON)) {

            private static final long serialVersionUID = -2790668001235140089L;

            @Override
            public void actionPerformed(ActionEvent e) {
                Object oldVal = pref.get();
                action.actionPerformed(e);
                Object newVal = pref.get();
                if (!newVal.equals(oldVal))
                    logPrefChanged(log, pref);
            }
        };
    }

    public static void logPrefChanged(SwingLogPanel log, Pref< ? > pref) {
        if (log == null)
            return;
        log.log("Option ");
        log.logBold(pref.title);
        log.log(" changed to ");
        log.logBold(pref.get() + "\n");
        log.flush();
    }

    public static void logOnChange(final SwingLogPanel log, final Pref< ? >... prefs) {
        if (log == null)
            return;
        for (final Pref< ? > pref : prefs) {
            pref.addChangeListener(new ChangeListener() {

                @Override
                public void stateChanged(ChangeEvent e) {
                    logPrefChanged(log, pref);
                }
            });
        }
    }

    public static void main(String[] args) {
        SwingUtilities.invokeLater(new Runnable() {

            @Override
            public void run() {
                PreferencesDialog sd = new PreferencesDialog(null, null);
                sd.setDefaultCloseOperation(EXIT_ON_CLOSE);
                sd.setVisible(true);
            }
        });
    }

}
