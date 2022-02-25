package org.alloytools.json.util;

import java.io.IOException;
import java.io.OutputStream;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import org.alloytools.alloy.core.api.IAtom;
import org.alloytools.alloy.core.api.IRelation;
import org.alloytools.alloy.core.api.ITuple;

import aQute.lib.json.Encoder;
import aQute.lib.json.JSONCodec;

public class JSONEncoder {

    final static JSONCodec codec = new JSONCodec();

    public static void stream(OutputStream out, IRelation r) throws Exception {
        List<List<String>> data = getData(r);
        enc().to(out).put(data);
    }

    private static Encoder enc() {
        Encoder enc = codec.enc();
        enc.indent(" ");
        return enc;
    }

    public static void stream(Writer out, IRelation r) throws IOException, Exception {
        List<List<String>> data = getData(r);
        enc().to(out).put(data);
    }

    public static void stream(Writer out, Map<String,IRelation> r) throws IOException, Exception {
        Map<String,List<List<String>>> map = getData(r);
        enc().to(out).put(map);
    }

    public static void stream(OutputStream out, Map<String,IRelation> r) throws IOException, Exception {
        Map<String,List<List<String>>> map = getData(r);
        enc().to(out).put(map);
    }

    private static Map<String,List<List<String>>> getData(Map<String,IRelation> r) {
        Map<String,List<List<String>>> map = new TreeMap<>();
        r.forEach((k, v) -> map.put(k, getData(v)));
        return map;
    }

    private static List<List<String>> getData(IRelation r) {
        List<List<String>> data = new ArrayList<>();
        for (ITuple tuple : r) {
            List<String> atoms = new ArrayList<>();
            for (IAtom atom : tuple) {
                atoms.add(atom.getName());
            }
            data.add(atoms);
        }
        return data;
    }

}
