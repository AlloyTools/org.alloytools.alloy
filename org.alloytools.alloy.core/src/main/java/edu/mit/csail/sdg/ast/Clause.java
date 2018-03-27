package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Unfortunately not all objects are Expr. However, from the UI we want to be
 * able to locae the clauses in the text file and what they refer to.
 *
 * @author aqute
 *
 */
public interface Clause {

    /**
     * The position of this complete clause.
     */
    Pos pos();

    /**
     * Explain this clause for tooltips etc.
     *
     * @return a string formatted like a set
     */
    String explain();
}
