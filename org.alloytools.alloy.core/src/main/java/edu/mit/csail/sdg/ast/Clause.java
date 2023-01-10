package edu.mit.csail.sdg.ast;

import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Unfortunately not all objects are Expr. However, from the UI we want to be
 * able to locate the clauses in the text file and what they refer to.
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

    public final class Custom implements Clause{
        final Pos pos;
        final String explanation;

        public Custom(Pos pos, String explanation) {
            this.pos = pos;
            this.explanation = explanation;
        }

        @Override
        public Pos pos() {
            return pos;
        }

        @Override
        public String explain() {
            return explanation;
        }

    }
}
