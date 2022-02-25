package org.alloytools.json.util;

import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.Map;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;

public class TextEncoder {

    public static void stream(OutputStream out, IRelation r) throws Exception {
        stream(new OutputStreamWriter(out, StandardCharsets.UTF_8), r);
    }

    public static void stream(Writer out, IRelation r) throws IOException, Exception {
        PrintWriter pw = new PrintWriter(out);
        pw.print("{");
        for (ITuple tuple : r) {
            if (tuple.arity() != 0) {
                pw.print("(");
                String del = "";
                for (IAtom atom : tuple) {
                    pw.print(del);
                    pw.print(atom.getName());
                }
                pw.print(")");
            }
        }
        pw.println("}");
    }

    public static void stream(Writer out, Map<String,IRelation> r) throws IOException, Exception {
        PrintWriter pw = new PrintWriter(out);
        for (Map.Entry<String,IRelation> e : r.entrySet()) {
            pw.printf("%-30s", e.getKey());
            stream(pw, e.getValue());
        }
    }

    public static void stream(OutputStream out, Map<String,IRelation> r) throws IOException, Exception {
        stream(new OutputStreamWriter(out, StandardCharsets.UTF_8), r);
    }

}
