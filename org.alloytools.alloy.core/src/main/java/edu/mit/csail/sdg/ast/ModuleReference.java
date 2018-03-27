package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

public class ModuleReference implements Clause {

    final Pos    pos;
    final String fileName;

    public ModuleReference(String fileName) {
        this.fileName = fileName;
        this.pos = new Pos(fileName, 1, 1, 1, 1);
    }

    @Override
    public Pos pos() {
        return pos;
    }

    public String getFileName() {
        return fileName;
    }

    @Override
    public String toString() {
        return "module " + fileName;
    }

    @Override
    public String explain() {
        return toString();
    }
}
