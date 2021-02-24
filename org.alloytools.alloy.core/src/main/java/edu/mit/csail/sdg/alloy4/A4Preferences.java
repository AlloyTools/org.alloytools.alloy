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

import java.awt.GraphicsEnvironment;
import java.awt.event.ActionEvent;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.prefs.Preferences;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.DefaultSingleSelectionModel;
import javax.swing.Icon;

import edu.mit.csail.sdg.translator.A4Options.SatSolver;

/**
 *
 * @modified [electrum] added decompose strategy option
 *
 */
@SuppressWarnings({
                   "serial", "unchecked"
} )
public class A4Preferences {

    /** Base class for holding a single preference */
    public abstract static class Pref<T> extends DefaultSingleSelectionModel {

        /** The id associated with this preference. */
        public final String id;

        public String       title;
        public String       desc;

        /**
         * Constructors a new BooleanPref object with the given id.
         */
        public Pref(String id) {
            this(id, id);
        }

        public Pref(String id, String title) {
            this(id, title, title);
        }

        public Pref(String id, String title, String desc) {
            this.id = id;
            this.title = title;
            this.desc = desc;
        }

        /**
         * Reads the value for this preference; if not set or is empty, we return the
         * default value.
         */
        public T get() {
            String ans = Preferences.userNodeForPackage(Util.class).get(id, "");
            T ret = (ans != null && ans.length() > 0) ? ret = parse(ans) : null;
            return (ret != null) ? ret : defaultValue();
        }

        /** Sets the value for this preference. */
        public void set(T value) {
            T oldValue = get();
            String str = serialize(value);
            assert value != null && parse(str) != null;
            Preferences.userNodeForPackage(Util.class).put(id, str);
            if (!oldValue.equals(value))
                fireStateChanged();
        }

        @Override
        public void setSelectedIndex(int index) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int getSelectedIndex() {
            return 0;
        }

        /** Returns the default value of this preference. */
        protected abstract T defaultValue();

        /**
         * Returns a serialized (string) version of the given value that will be
         * persisted using {@link Preferences}.
         */
        protected String serialize(T value) {
            return value.toString();
        }

        /**
         * Parses a given string value into the original type (T) of this preference.
         */
        protected abstract T parse(String str);
    }

    /**
     * This reads and writes multi-choice persistent preferences.
     */
    public static class ChoicePref<T> extends Pref<T> {

        private final List<T> validChoices;
        private final T       defaultValue;

        public ChoicePref(String id, T[] validChoices, T... defValueCandidates) {
            this(id, Arrays.asList(validChoices), defValueCandidates);
        }

        public ChoicePref(String id, Iterable<T> validChoices, T... defValueCandidates) {
            this(id, id, id, validChoices, defValueCandidates);
        }

        public ChoicePref(String id, String title, Iterable<T> validChoices, T... defValueCandidates) {
            this(id, title, title, validChoices, defValueCandidates);
        }

        public ChoicePref(String id, String title, String desc, Iterable<T> validChoices, T... defValueCandidates) {
            super(id, title, desc);
            if (validChoices == null) {
                assert new Exception().getStackTrace()[1].getClassName().endsWith(DelayedChoicePref.class.getName());
                this.validChoices = null;
                this.defaultValue = null;
            } else {
                Object[] x = checkChoices(validChoices, defValueCandidates);
                this.validChoices = (List<T>) x[0];
                this.defaultValue = (T) x[1];
            }
        }

        @Override
        public void setSelectedIndex(int index) {
            set(validChoices().get(index));
        }

        @Override
        public int getSelectedIndex() {
            return index(get());
        }

        protected Object[] checkChoices(Iterable<T> validChoices, T[] defValueCandidates) {
            List<T> lst = new ArrayList<T>();
            for (T t : validChoices)
                lst.add(t);
            T defaultValue = null;
            for (T defVal : defValueCandidates) {
                if (lst.contains(defVal)) {
                    defaultValue = defVal;
                    break;
                }
            }
            if (defaultValue == null) {
                defaultValue = lst.get(0);
            }
            return new Object[] {
                                 Collections.unmodifiableList(lst), defaultValue
            };
        }

        /**
         * Returns a list of valid choices for this multi-choice preference
         */
        public List<T> validChoices() {
            return validChoices;
        }

        /**
         * Returns the index of the given value (choice) in the list of all valid
         * choices
         */
        public int index(T value) {
            return validChoices.indexOf(get());
        }

        @Override
        protected String serialize(T value) {
            return value.toString();
        }

        @Override
        protected T parse(String str) {
            for (T t : validChoices()) {
                if (serialize(t).equals(str))
                    return t;
            }
            return null;
        }

        @Override
        protected T defaultValue() {
            return defaultValue;
        }

        public Action getAction(final T value) {
            return new AbstractAction() {

                @Override
                public void actionPerformed(ActionEvent e) {
                    set(value);
                }
            };
        }

        public Object renderValueShort(T value) {
            return value;
        }

        public Object renderValueLong(T value) {
            return renderValueShort(value);
        }
    }

    /**
     * Provides a way to delay supplying valid choices and a default value
     */
    public static class DelayedChoicePref<T> extends ChoicePref<T> {

        private List<T> validChoices2;
        private T       defaultValue2;

        public DelayedChoicePref(String id) {
            this(id, id, id);
        }

        public DelayedChoicePref(String id, String title) {
            this(id, title, title);
        }

        public DelayedChoicePref(String id, String title, String desc) {
            super(id, title, desc, null, ((T) new Object[] {}));
        }

        public DelayedChoicePref(String id, Iterable<T> validChoices, T... defValueCandidates) {
            super(id, validChoices, defValueCandidates);
        }

        public DelayedChoicePref(String id, String title, Iterable<T> validChoices, T... defValueCandidates) {
            super(id, title, validChoices, defValueCandidates);
        }

        public DelayedChoicePref(String id, String title, String desc, Iterable<T> validChoices, T... defValueCandidates) {
            super(id, title, desc, validChoices, defValueCandidates);
        }

        public void setChoices(Iterable<T> validChoices, T... defValueCandidates) {
            Object[] x = checkChoices(validChoices, defValueCandidates);
            this.validChoices2 = (List<T>) x[0];
            this.defaultValue2 = (T) x[1];
        }

        @Override
        protected T defaultValue() {
            return defaultValue2 != null ? defaultValue2 : super.defaultValue();
        }

        @Override
        public List<T> validChoices() {
            return validChoices2 != null ? validChoices2 : super.validChoices();
        }
    }

    /**
     * This reads and writes IntChoice-valued Java persistent preferences.
     */
    public static class IntChoicePref extends ChoicePref<Integer> {

        public IntChoicePref(String id, Iterable<Integer> validChoices, Integer defaultValue) {
            super(id, validChoices, defaultValue);
        }

        public IntChoicePref(String id, String title, Iterable<Integer> validChoices, Integer defaultValue) {
            super(id, title, validChoices, defaultValue);
        }

        public IntChoicePref(String id, String title, String desc, Iterable<Integer> validChoices, Integer defaultValue) {
            super(id, title, desc, validChoices, defaultValue);
        }

        public static IntChoicePref range(String id, int min, int step, int max, int defaultValue) {
            return range(id, id, id, min, step, max, defaultValue);
        }

        public static IntChoicePref range(String id, String title, int min, int step, int max, int defaultValue) {
            return range(id, title, title, min, step, max, defaultValue);
        }

        public static IntChoicePref range(String id, String title, String desc, int min, int step, int max, int defaultValue) {
            ArrayList<Integer> lst = new ArrayList<Integer>();
            for (int x = min; x <= max; x += step) {
                lst.add(x);
            }
            return new IntChoicePref(id, title, desc, lst, defaultValue);
        }
    }

    /**
     * This reads and writes StringChoice-valued Java persistent preferences.
     */
    public static class StringChoicePref extends ChoicePref<String> {

        public StringChoicePref(String id, Iterable<String> validChoices, String... defaultValueCandidates) {
            super(id, validChoices, defaultValueCandidates);
        }

        public StringChoicePref(String id, String title, Iterable<String> validChoices, String... defaultValueCandidates) {
            super(id, title, validChoices, defaultValueCandidates);
        }

        public StringChoicePref(String id, String title, String desc, Iterable<String> validChoices, String... defaultValueCandidates) {
            super(id, title, desc, validChoices, defaultValueCandidates);
        }
    }

    /**
     * This reads and writes String-valued Java persistent preferences.
     * <p>
     * <b>Thread Safety:</b> Safe.
     */
    public static final class StringPref extends Pref<String> {

        /** The default value for this preference. */
        private final String defaultValue;

        /** Constructs a new StringPref object with the given id. */
        public StringPref(String id) {
            super(id);
            this.defaultValue = "";
        }

        /**
         * Constructs a new StringPref object with the given id and the given default
         * value.
         */
        public StringPref(String id, String defaultValue) {
            super(id);
            this.defaultValue = defaultValue;
        }

        @Override
        protected String serialize(String value) {
            return value;
        }

        @Override
        protected String parse(String str) {
            return str;
        }

        @Override
        protected String defaultValue() {
            return defaultValue;
        }
    }

    /**
     * This reads and writes boolean-valued Java persistent preferences.
     * <p>
     * <b>Thread Safety:</b> Safe.
     */
    public static final class BooleanPref extends Pref<Boolean> {

        private final boolean defaultValue;

        public BooleanPref(String id, String title, String desc, boolean defaultValue) {
            super(id, title, desc);
            this.defaultValue = defaultValue;
        }

        public BooleanPref(String id, String title, String desc) {
            this(id, title, desc, false);
        }

        public BooleanPref(String id, String title, boolean defaultValue) {
            super(id, title);
            this.defaultValue = defaultValue;
        }

        public BooleanPref(String id, String title) {
            this(id, title, false);
        }

        public BooleanPref(String id, boolean defaultValue) {
            super(id);
            this.defaultValue = defaultValue;
        }

        public BooleanPref(String id) {
            this(id, false);
        }

        @Override
        protected String serialize(Boolean value) {
            return value ? "y" : "n";
        }

        @Override
        protected Boolean parse(String str) {
            return "y".equals(str);
        }

        @Override
        protected Boolean defaultValue() {
            return defaultValue;
        }

        /** Toggles the value for this preference. */
        public void toggle() {
            set(!get());
        }

        public BooleanAction getAction(String title) {
            return new BooleanAction(this, title);
        }

        public BooleanAction getTitleAction() {
            return getAction(title);
        }

        public BooleanAction getDescAction() {
            return getAction(desc);
        }
    }

    /**
     * This reads and writes integer-valued Java persistent preferences.
     * <p>
     * <b>Thread Safety:</b> Safe.
     */
    public static final class IntPref extends Pref<Integer> {

        /** The minimum value for this preference. */
        public final int min;
        /** The maximum value for this preference. */
        public final int max;
        /** The default value for this preference. */
        public final int def;

        /**
         * If min>n, we return min; else if n>max, we return max; otherwise we return n.
         */
        private int bound(int n) {
            return n < min ? min : (n > max ? max : n);
        }

        /**
         * Make a new IntPref object with the given id; you must ensure max >= min, but
         * def does not have to be between min..max
         */
        public IntPref(String id, int min, int def, int max) {
            super(id);
            this.min = min;
            this.def = def;
            this.max = max;
        }

        @Override
        protected String serialize(Integer value) {
            return "" + bound(value);
        }

        @Override
        protected Integer parse(String str) {
            return bound(Integer.parseInt(str));
        }

        @Override
        protected Integer defaultValue() {
            return def;
        }
    }

    /** A simple action tied to a boolean preference */
    public static final class BooleanAction extends AbstractAction {

        private static final long serialVersionUID = -7357369720337054603L;
        private final BooleanPref pref;

        public BooleanAction(BooleanPref pref) {
            this(pref, null, null);
        }

        public BooleanAction(BooleanPref pref, String name) {
            this(pref, name, null);
        }

        public BooleanAction(BooleanPref pref, String name, Icon icon) {
            super(name, icon);
            this.pref = pref;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            pref.toggle();
        }
    }

    // ======== The Preferences
    // ======================================================================================//
    // ======== Note: you must make sure each preference has a unique key
    // ============================================//

    /**
     * True if Alloy Analyzer should let warning be nonfatal.
     */
    public static final BooleanPref           WarningNonfatal        = new BooleanPref("WarningNonfatal", "Allow warnings");

    /**
     * True if Alloy Analyzer should automatically visualize the latest instance.
     */
    public static final BooleanPref           AutoVisualize          = new BooleanPref("AutoVisualize", "Visualize automatically");

    /** True if Alloy Analyzer should insist on antialias. */
    public static final BooleanPref           AntiAlias              = new BooleanPref("AntiAlias", "Use anti-aliasing");

    /**
     * True if Alloy Analyzer should record the raw Kodkod input and output.
     */
    public static final BooleanPref           RecordKodkod           = new BooleanPref("RecordKodkod", "Record the Kodkod input/output");

    /**
     * True if Alloy Analyzer should enable the new Implicit This name resolution.
     */
    public static final BooleanPref           ImplicitThis           = new BooleanPref("ImplicitThis", "Enable 'implicit this' name resolution");

    /**
     * True if Alloy Analyzer should not report models that overflow.
     */
    public static final BooleanPref           NoOverflow             = new BooleanPref("NoOverflow", "Prevent overflows", true);

    /**
     * The latest X coordinate of the Alloy Analyzer's main window.
     */
    public static final IntPref               AnalyzerX              = new IntPref("AnalyzerX", 0, -1, 65535);

    /**
     * The latest Y coordinate of the Alloy Analyzer's main window.
     */
    public static final IntPref               AnalyzerY              = new IntPref("AnalyzerY", 0, -1, 65535);

    /** The latest width of the Alloy Analyzer's main window. */
    public static final IntPref               AnalyzerWidth          = new IntPref("AnalyzerWidth", 0, -1, 65535);

    /**
     * The latest height of the Alloy Analyzer's main window.
     */
    public static final IntPref               AnalyzerHeight         = new IntPref("AnalyzerHeight", 0, -1, 65535);

    /** The latest font size of the Alloy Analyzer. */
    public static final IntChoicePref         FontSize               = new IntChoicePref("FontSize", "Font size", Arrays.asList(9, 10, 11, 12, 14, 16, 18, 20, 22, 24, 26, 28, 32, 36, 40, 44, 48, 54, 60, 66, 72), 14);

    /** The latest font name of the Alloy Analyzer. */
    public static final StringChoicePref      FontName               = new StringChoicePref("FontName", "Font family", Arrays.asList(GraphicsEnvironment.getLocalGraphicsEnvironment().getAvailableFontFamilyNames()), "Lucida Grande");

    /** The latest tab distance of the Alloy Analyzer. */
    public static final IntChoicePref         TabSize                = IntChoicePref.range("TabSize", "Tab size", 1, 1, 16, 4);

    /** The latest welcome screen that the user has seen. */
    public static final BooleanPref           Welcome                = new BooleanPref("Welcome", "Show welcome message at start up");

    /** Look and feel */
    public static final StringChoicePref      LAF                    = new StringChoicePref("LAF", "Look and feel", Arrays.asList("Native", "Cross-platform"), Util.onMac() || Util.onWindows() ? "Native" : "Cross-platform");

    /**
     * Whether syntax highlighting should be disabled or not.
     */
    public static final BooleanPref           SyntaxDisabled         = new BooleanPref("SyntaxHighlightingDisabled", "Disable syntax highlighting");

    /** The number of recursion unrolls. */
    public static final IntChoicePref         Unrolls                = new IntChoicePref("Unrolls", "Recursion depth", Arrays.asList(-1, 0, 1, 2, 3), -1) {

                                                                         @Override
                                                                         public Object renderValueShort(Integer value) {
                                                                             return (value != null && value.intValue() == -1) ? "disabled" : value;
                                                                         }
                                                                     };

    /** The skolem depth. */
    public static final IntChoicePref         SkolemDepth            = new IntChoicePref("SkolemDepth3", "Skolem depth", Arrays.asList(0, 1, 2, 3, 4), 1);

    /** The unsat core minimization strategy. */
    private static final String[]             coreMinimizationLabels = new String[] {
                                                                                     "Slow", "Slow (guarantees local minimum)", "Medium", "Medium", "Fast", "Fast (initial unsat core)"
    };
    public static final IntChoicePref         CoreMinimization       = new IntChoicePref("CoreMinimization", "Unsat core minimization", Arrays.asList(0, 1, 2), 2) {

                                                                         @Override
                                                                         public Object renderValueShort(Integer value) {
                                                                             return coreMinimizationLabels[value * 2];
                                                                         }

                                                                         @Override
                                                                         public Object renderValueLong(Integer value) {
                                                                             return coreMinimizationLabels[value * 2 + 1];
                                                                         }
                                                                     };

    private static final String[]             coreGranularityLabels  = new String[] {
                                                                                     "Top-level", "Top-level conjuncts only", "Flatten once", "Flatten the formula once at the beginning", "Flatten twice", "Flatten the formula at the beginning and after skolemizing", "Expand quantifiers", "In addition to flattening the formula twice, expand the quantifiers"
    };
    /** The unsat core granularity. */
    public static final IntChoicePref         CoreGranularity        = new IntChoicePref("CoreGranularity", "Unsat core granularity", Arrays.asList(0, 1, 2, 3), 0) {

                                                                         @Override
                                                                         public Object renderValueShort(Integer value) {
                                                                             return coreGranularityLabels[value * 2];
                                                                         }

                                                                         @Override
                                                                         public Object renderValueLong(Integer value) {
                                                                             return coreGranularityLabels[value * 2 + 1];
                                                                         }
                                                                     };

    /** The decompose solving strategy. */
    public static final ChoicePref<Decompose> DecomposePref          = new ChoicePref<Decompose>("Decompose strategy", Decompose.values(), Decompose.OFF) {

                                                                         @Override
                                                                         protected String serialize(Decompose value) {
                                                                             return value.id;
                                                                         }
                                                                     };

    public enum Decompose {
                           /** regular amalgamated strategy. */
                           OFF("0", "batch"),
                           /** hybrid strategy, competitive parallel vs amalgamated. */
                           HYBRID("1", "hybrid"),
                           /** purely parallel decompose strategy. */
                           PARALLEL("2", "parallel");

        /** Returns true if it is greater than or equal to "other". */
        public boolean geq(Decompose other) {
            return ordinal() >= other.ordinal();
        }

        /**
         * This is a unique String for this value; it should be kept consistent in
         * future versions.
         */
        private final String id;
        /** This is the label that the toString() method will return. */
        private final String label;

        /** Constructs a new Decompose value with the given id and label. */
        private Decompose(String id, String label) {
            this.id = id;
            this.label = label;
        }

        /** Returns the human-readable label for this enum value. */
        @Override
        public final String toString() {
            return label;
        }
    }

    /**
     * The amount of memory (in M) to allocate for Kodkod and the SAT solvers.
     */
    public static final IntChoicePref                SubMemory            = new IntChoicePref("SubMemory", "Maximum memory", Arrays.asList(768, 1024, 1536, 2048, 2560, 3072, 3584, 4096, 8192, 16384), 2084) {

                                                                              @Override
                                                                              public Object renderValueShort(Integer value) {
                                                                                  return value.toString() + " MB";
                                                                              }
                                                                          };

    /**
     * The amount of stack (in K) to allocate for Kodkod and the SAT solvers.
     */
    public static final IntChoicePref                SubStack             = new IntChoicePref("SubStack", "Maximum stack", Arrays.asList(1024, 2048, 4096, 8192, 16384, 32768, 65536), 8192) {

                                                                              @Override
                                                                              public Object renderValueShort(Integer value) {
                                                                                  return value.toString() + " k";
                                                                              }
                                                                          };

    /**
     * The first file in Alloy Analyzer's "open recent" list.
     */
    public static final StringPref                   Model0               = new StringPref("Model0");

    /**
     * The second file in Alloy Analyzer's "open recent" list.
     */
    public static final StringPref                   Model1               = new StringPref("Model1");

    /**
     * The third file in Alloy Analyzer's "open recent" list.
     */
    public static final StringPref                   Model2               = new StringPref("Model2");

    /**
     * The fourth file in Alloy Analyzer's "open recent" list.
     */
    public static final StringPref                   Model3               = new StringPref("Model3");

    /** Automatically infer partial instance from model */
    public static final BooleanPref                  InferPartialInstance = new BooleanPref("InferPartialInstance", "Infer partial instance");

    public static final DelayedChoicePref<SatSolver> Solver               = new DelayedChoicePref<SatSolver>("SatSolver2", "Solver", SatSolver.values(), SatSolver.SAT4J) {

                                                                              @Override
                                                                              protected String serialize(SatSolver value) {
                                                                                  return value.id();
                                                                              }
                                                                          };

    public static final ChoicePref<Verbosity>        VerbosityPref        = new ChoicePref<Verbosity>("Verbosity", Verbosity.values(), Verbosity.DEFAULT) {

                                                                              @Override
                                                                              protected String serialize(Verbosity value) {
                                                                                  return value.id;
                                                                              }
                                                                          };

    public enum Verbosity {
                           /** Level 0. */
                           DEFAULT("0", "low"),
                           /** Level 1. */
                           VERBOSE("1", "medium"),
                           /** Level 2. */
                           DEBUG("2", "high"),
                           /** Level 3. */
                           FULLDEBUG("3", "debug");

        /**
         * Returns true if it is greater than or equal to "other".
         */
        public boolean geq(Verbosity other) {
            return ordinal() >= other.ordinal();
        }

        /**
         * This is a unique String for this value; it should be kept consistent in
         * future versions.
         */
        private final String id;
        /**
         * This is the label that the toString() method will return.
         */
        private final String label;

        /**
         * Constructs a new Verbosity value with the given id and label.
         */
        private Verbosity(String id, String label) {
            this.id = id;
            this.label = label;
        }

        /**
         * Given an id, return the enum value corresponding to it (if there's no match,
         * then return DEFAULT).
         */
        /** Returns the human-readable label for this enum value. */
        @Override
        public final String toString() {
            return label;
        }
    }

    public static Pref< ? >[] nonUserPrefs = new Pref< ? >[] {
                                                              AnalyzerX, AnalyzerHeight, AnalyzerWidth, AnalyzerY, Model0, Model1, Model2, Model3
    };

    public static List<Pref< ? >> allPrefs() {
        List<Pref< ? >> ans = new ArrayList<A4Preferences.Pref< ? >>();
        Class<A4Preferences> self = A4Preferences.class;
        for (Field f : self.getDeclaredFields()) {
            if (Pref.class.isAssignableFrom(f.getType())) {
                try {
                    ans.add((Pref< ? >) f.get(self));
                } catch (Exception e) {
                }
            }
        }
        return ans;
    }

    public static List<Pref< ? >> allUserPrefs() {
        List<Pref< ? >> ans = allPrefs();
        for (Pref< ? > p : nonUserPrefs)
            ans.remove(p);
        return ans;
    }

    // /** The visualization algorithm */
    // public static final StringChoicePref VisualizationAlgorithm = new
    // StringChoicePref("VizAlg", "Visualization algorightm",
    // Arrays.asList("Sugiyama", "Circle", "Grid"), "Sugiyama");
    //
    // public static final IntPref GridLayoutRows = new
    // IntPref("GridLayoutRows", 1, 5, 100);
    // public static final IntPref GridLayoutCols = new
    // IntPref("GridLayoutCols", 1, 5, 100);

}
