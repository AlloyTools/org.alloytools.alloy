package ca.uwaterloo.watform.ast;


import edu.mit.csail.sdg.alloy4.Pos;

public class Dash  {
	// methods that all of Dash AST should have

   /**
     * The filename, line, and column position in the original Alloy model file
     * (cannot be null).
     */
    public Pos pos;

    public final Pos getPos() {
        return pos;
    }

}