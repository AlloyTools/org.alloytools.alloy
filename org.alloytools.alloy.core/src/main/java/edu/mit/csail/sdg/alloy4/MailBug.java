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
import java.awt.Dimension;
import java.io.BufferedInputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.Thread.UncaughtExceptionHandler;
import java.net.URL;
import java.net.URLConnection;
import java.util.Map;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;

import org.alloytools.alloy.core.AlloyCore;

/**
 * This class asks the user for permission to email a bug report when an
 * uncaught exception occurs.
 */

public final class MailBug implements UncaughtExceptionHandler, Runnable {

    /**
     * The version number of the most recent Alloy4 (as queried from alloy.mit.edu);
     * -1 if alloy.mit.edu has not replied yet.
     */
    private static int          latestAlloyVersion     = -1;

    /**
     * The name of the most recent Alloy4 (as queried from alloy.mit.edu); "unknown"
     * if alloy.mit.edu has not replied yet.
     */
    private static String       latestAlloyVersionName = "unknown";

    /** The URL where the bug report should be sent. */
    private static final String ALLOY_URL              = "http://alloy.mit.edu/postbug4.php";

    /**
     * The URL where the current version info can be queried.
     */
    private static final String ALLOY_NOW              = "http://alloy.mit.edu/alloy4/download/alloy4.txt";

    /**
     * If alloy.mit.edu has replied, then return the latest Alloy build number, else
     * return -1.
     */
    public static int latestBuildNumber() {
        synchronized (MailBug.class) {
            return latestAlloyVersion;
        }
    }

    /**
     * If alloy.mit.edu has replied, then return the latest Alloy build name, else
     * return "unknown"
     */
    public static String latestBuildName() {
        synchronized (MailBug.class) {
            return latestAlloyVersionName;
        }
    }

    /** Construct a new MailBug object. */
    private MailBug() {}

    /**
     * Setup the uncaught-exception-handler and use a separate thread to query
     * alloy.mit.edu for latest version number.
     */
    public static void setup() {
        if (AlloyCore.isDebug())
            return;

        if (Thread.getDefaultUncaughtExceptionHandler() != null)
            return;
        MailBug x = new MailBug();
        Thread.setDefaultUncaughtExceptionHandler(x);
        new Thread(x).start();
    }

    /**
     * This method concatenates a Throwable's message and stack trace and all its
     * causes into a single String.
     */
    public static String dump(Throwable ex) {
        StringBuilder sb = new StringBuilder();
        while (ex != null) {
            sb.append(ex.getClass()).append(": ").append(ex.getMessage()).append('\n');
            StackTraceElement[] trace = ex.getStackTrace();
            if (trace != null)
                for (int n = trace.length, i = 0; i < n; i++)
                    sb.append(trace[i]).append('\n');
            ex = ex.getCause();
            if (ex != null)
                sb.append("caused by...\n");
        }
        return sb.toString().trim();
    }

    /**
     * This method returns true if the exception appears to be a Sun Java GUI bug.
     */
    private static boolean isGUI(Throwable ex) {
        // If the root of the stack trace is within Java framework itself,
        // and no where is Alloy, Kodkod, or SAT4J anywhere along the trace,
        // then it's almost *always* a Sun Java GUI bug from what we've seen.
        // And it's better to ignore it rather than kill the file that the user
        // is editing.
        while (ex != null) {
            StackTraceElement[] trace = ex.getStackTrace();
            for (int n = (trace == null ? 0 : trace.length), i = 0; i < n; i++) {
                String name = trace[i].getClassName();
                if (!name.startsWith("java.") && !name.startsWith("javax.") && !name.startsWith("sun."))
                    return false;
            }
            ex = ex.getCause();
        }
        return true;
    }

    /** This method prepares the crash report. */
    private static String prepareCrashReport(Thread thread, Throwable ex, String email, String problem) {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        pw.printf("Alloy Analyzer %s crash report (Build Date = %s) (Commit = %s)\n", Version.version(), Version.commit);
        pw.printf("\n========================= Email ============================\n%s\n", Util.convertLineBreak(email).trim());
        pw.printf("\n========================= Problem ==========================\n%s\n", Util.convertLineBreak(problem).trim());
        pw.printf("\n========================= Thread Name ======================\n%s\n", thread.getName().trim());
        if (ex != null)
            pw.printf("\n========================= Stack Trace ======================\n%s\n", dump(ex));
        pw.printf("\n========================= Preferences ======================\n");
        try {
            for (String key : Preferences.userNodeForPackage(Util.class).keys()) {
                String value = Preferences.userNodeForPackage(Util.class).get(key, "");
                pw.printf("%s = %s\n", key.trim(), value.trim());
            }
        } catch (BackingStoreException bse) {
            pw.printf("BackingStoreException occurred: %s\n", bse.toString().trim());
        }
        pw.printf("\n========================= System Properties ================\n");
        pw.println("Runtime.freeMemory() = " + Runtime.getRuntime().freeMemory());
        pw.println("nRuntime.totalMemory() = " + Runtime.getRuntime().totalMemory());
        for (Map.Entry<Object,Object> e : System.getProperties().entrySet()) {
            String k = String.valueOf(e.getKey()), v = String.valueOf(e.getValue());
            pw.printf("%s = %s\n", k.trim(), v.trim());
        }
        pw.printf("\n========================= The End ==========================\n\n");
        pw.close();
        sw.flush();
        return sw.toString();
    }

    /**
     * This method opens a connection then read the entire content (it converts
     * non-ASCII into '?'); if error occurred it returns "".
     *
     * @param URL - the remote URL we want to read from
     * @param send - if nonempty we will send it to the remote URL before attempting
     *            to read from the remote URL
     */
    private static String readAll(String URL, String send, String failure) {
        BufferedInputStream bis = null;
        InputStream in = null;
        OutputStream out = null;
        String ans;
        try {
            URLConnection connection = new URL(URL).openConnection();
            if (send != null && send.length() > 0) {
                connection.setDoOutput(true);
                out = connection.getOutputStream();
                out.write(send.getBytes("UTF-8"));
                out.close();
                out = null;
            }
            in = connection.getInputStream();
            bis = new BufferedInputStream(in);
            StringBuilder sb = new StringBuilder();
            int i;
            while ((i = bis.read()) >= 0) {
                sb.append((char) (i <= 0x7F ? i : '?'));
            }
            ans = Util.convertLineBreak(sb.toString());
        } catch (Throwable ex) {
            ans = failure;
        } finally {
            Util.close(bis);
            Util.close(in);
            Util.close(out);
        }
        return ans;
    }

    /**
     * This method will query alloy.mit.edu for the latest version number.
     */
    @Override
    public void run() {
        String result = readAll(ALLOY_NOW + "?buildnum=" + Version.buildNumber() + "&builddate=" + Version.buildDate(), "", "");
        if (!result.startsWith("Alloy Build "))
            return;
        // Now that we know we're online, try to remove the old ill-conceived
        // "Java WebStart" versions of Alloy4 BETA1..BETA7
        // Subprocess.exec(20000, new String[]{
        // "javaws", "-silent", "-offline", "-uninstall",
        // "http://alloy.mit.edu/alloy4/download/alloy4.jnlp"});
        // Now parse the result
        int num = 0;
        boolean found = false;
        for (int i = 0, len = result.length();; i++) {
            if (i >= len)
                return; // malformed
            char c = result.charAt(i);
            if (!(c >= '0' && c <= '9')) {
                if (!found)
                    continue;
                else {
                    result = result.substring(i).trim();
                    break;
                }
            }
            found = true;
            num = num * 10 + (c - '0');
        }
        synchronized (MailBug.class) {
            latestAlloyVersionName = result;
            latestAlloyVersion = num;
        }
    }

    /**
     * This method sends the crash report then displays alloy.mit.edu's reply in a
     * text window.
     */
    private static void sendCrashReport(Thread thread, Throwable ex, String email, String problem) {
        try {
            final String report = prepareCrashReport(thread, ex, email, problem);
            final String alt = "Sorry. An error has occurred in posting the bug report.\n" + "Please email this report to alloy@mit.edu directly.\n\n" + dump(ex);
            final JTextArea status = OurUtil.textarea("Sending the bug report... please wait...", 10, 40, false, true, new LineBorder(Color.GRAY));
            new Thread(new Runnable() {

                @Override
                public void run() {
                    final String output = readAll(ALLOY_URL, report, alt);
                    SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                            status.setText(output);
                            status.setCaretPosition(0);
                        }
                    });
                }
            }).start();
            OurDialog.showmsg("Sending the bug report... please wait...", status);
        } finally {
            System.exit(1);
        }
    }

    /**
     * This method is an exception handler for uncaught exceptions.
     */
    @Override
    public void uncaughtException(Thread thread, Throwable ex) {
        if (isGUI(ex))
            return;
        final int ver;
        final String name;
        synchronized (MailBug.class) {
            ver = latestAlloyVersion;
            name = latestAlloyVersionName;
        }
        if (ex != null) {
            System.out.flush();
            System.err.flush();
            System.err.println("Exception: " + ex.getClass());
            System.err.println("Message: " + ex);
            System.err.println("Stacktrace:");
            System.err.println(dump(ex));
            System.err.flush();
        }
        final String yes = "Send the Bug Report", no = "Don't Send the Bug Report";
        final JTextField email = OurUtil.textfield("", 20, new LineBorder(Color.DARK_GRAY));
        final JTextArea problem = OurUtil.textarea("", 50, 50, true, false, new EmptyBorder(0, 0, 0, 0));
        final JScrollPane scroll = OurUtil.scrollpane(problem, new LineBorder(Color.DARK_GRAY), new Dimension(300, 200));
        for (Throwable ex2 = ex; ex2 != null; ex2 = ex2.getCause()) {
            if (ex2 instanceof StackOverflowError)
                OurDialog.fatal(new Object[] {
                                              "Sorry. The Alloy Analyzer has run out of stack space.", " ", "Try simplifying your model or reducing the scope.", "And try reducing Options->SkolemDepth to 0.", "And try increasing Options->Stack.", " ", "There is no way for Alloy to continue execution, so pressing OK will shut down Alloy."
                });
            if (ex2 instanceof OutOfMemoryError)
                OurDialog.fatal(new Object[] {
                                              "Sorry. The Alloy Analyzer has run out of memory.", " ", "Try simplifying your model or reducing the scope.", "And try reducing Options->SkolemDepth to 0.", "And try increasing Options->Memory.", " ", "There is no way for Alloy to continue execution, so pressing OK will shut down Alloy."
                });
        }
        if (ver > Version.buildNumber())
            OurDialog.fatal(new Object[] {
                                          "Sorry. A fatal error has occurred.", " ", "You are running Alloy Analyzer " + Version.version(), "but the most recent is Alloy Analyzer " + name, " ", "Please try to upgrade to the newest version", "as the problem may have already been fixed.", " ", "There is no way for Alloy to continue execution, so pressing OK will shut down Alloy."
            });
        if (OurDialog.yesno(new Object[] {
                                          "Sorry. A fatal internal error has occurred.", " ", "You may submit a bug report (via HTTP).", "The error report will include your system", "configuration, but no other information.", " ", "If you'd like to be notified about a fix,", "please describe the problem and enter your email address.", " ", OurUtil.makeHT("Email:", 5, email, null), OurUtil.makeHT("Problem:", 5, scroll, null)
        }, yes, no))
            sendCrashReport(thread, ex, email.getText(), problem.getText());
        System.exit(1);
    }
}
