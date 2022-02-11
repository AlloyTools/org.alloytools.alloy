package org.alloytools.alloy.classic.provider;

import org.alloytools.alloy.core.api.CompilerMessage;
import org.alloytools.alloy.core.api.Position;


public class ClassicCompilerMessage implements CompilerMessage {

    final String   path;
    final String   source;
    final String   msg;
    final Position pos;

    public ClassicCompilerMessage(String path, String source, String msg, Position pos) {
        this.path = path;
        this.source = source;
        this.msg = msg;
        this.pos = pos;
    }

    @Override
    public String getMessage() {
        return msg;
    }

    @Override
    public String getSource() {
        return source;
    }

    @Override
    public Position getPosition() {
        return pos;
    }

    @Override
    public String toString() {
        return "[path=" + path + ", msg=" + msg + ", pos=" + pos + "]";
    }

}
