package org.sat4j.tools;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

public class FileBasedVisualizationTool implements IVisualizationTool {

    private String filename;
    private PrintStream out;

    public FileBasedVisualizationTool(String filename) {
        this.filename = filename;
        updateWriter();
    }

    public void updateWriter() {
        try {
            this.out = new PrintStream(new FileOutputStream(this.filename
                    + ".dat"));
        } catch (FileNotFoundException e) {
            this.out = System.out;
        }
    }

    public String getFilename() {
        return this.filename;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    public void addPoint(double x, double y) {
        this.out.println(x + "\t" + y);
    }

    public void addInvisiblePoint(double x, double y) {
        this.out.println("#" + x + "\t" + "1/0");
    }

    public void init() {
        updateWriter();
    }

    public void end() {
        this.out.close();
    }

}
