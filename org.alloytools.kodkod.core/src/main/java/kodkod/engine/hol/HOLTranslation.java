package kodkod.engine.hol;

import kodkod.ast.Formula;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.Translation;
import kodkod.instance.Bounds;

public abstract class HOLTranslation extends Translation {

    public static class HOLException extends RuntimeException {

        private static final long serialVersionUID = 3431754608057485603L;

        public HOLException() {}

        public HOLException(String message) {
            super(message);
        }
    }

    protected Reporter rep;
    protected int      depth;

    public HOLTranslation(Bounds bounds, Options options, int depth) {
        super(bounds, options);
        this.depth = depth;
        rep = options.reporter() != null ? options.reporter() : new AbstractReporter() {};
        // rep = new AbstractReporter() {
        // public void holLoopStart(HOLTranslation tr, Formula formula, Bounds
        // bounds) {
        // System.out.println("started: " + formula);
        // }
        // public void holCandidateFound(HOLTranslation tr, Instance candidate)
        // {
        // System.out.println(" candidate found");
        // }
        // public void holVerifyingCandidate(HOLTranslation tr, Instance
        // candidate, Formula checkFormula, Bounds bounds) {
        // System.out.println(" verifying: " + checkFormula);
        // }
        // public void holCandidateVerified(HOLTranslation tr, Instance
        // candidate) {}
        // public void holCandidateNotVerified(HOLTranslation tr, Instance
        // candidate, Instance cex) {}
        // public void holFindingNextCandidate(HOLTranslation tr, Formula inc) {
        // System.out.println(" finding next: " + inc);
        // }
        // };
    }

    public abstract Formula formula();

    public abstract Translation getCurrentFOLTranslation();

    // TODO: override in subclasses!!!
    public Formula formulaWithInc() {
        return formula();
    };

    @Override
    public boolean trivial() {
        return false;
    }

    public HOLTranslation next(Formula formula, Bounds bounds) {
        throw new RuntimeException("not implemented");
    }

    public HOLTranslation next(Formula formula) {
        return next(formula, new Bounds(bounds.universe()));
    }

    public HOLTranslation next() {
        throw new RuntimeException("not implemented");
    }

    public boolean isFirstOrder() {
        return false;
    }

    public int depth() {
        return depth;
    }

    public abstract int numCandidates();
}
