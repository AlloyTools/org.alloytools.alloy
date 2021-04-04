package java_cup.runtime;

import edu.mit.csail.sdg.alloy4.Pos;

/**
 * Default Implementation for SymbolFactory, creates plain old Symbols
 *
 * @version last updated 27-03-2006
 * @author Michael Petter
 */

/*
 * ************************************************* class DefaultSymbolFactory
 * interface for creating new symbols
 ***************************************************/
public class DefaultSymbolFactory implements SymbolFactory {

    // Factory methods
    /**
     * DefaultSymbolFactory for CUP. Users are strongly encoraged to use
     * ComplexSymbolFactory instead, since it offers more detailed information about
     * Symbols in source code. Yet since migrating has always been a critical
     * process, You have the chance of still using the oldstyle Symbols.
     *
     * @deprecated as of CUP v11a replaced by the new runtime.ComplexSymbolFactory
     */
    // @deprecated
    @Deprecated
    public DefaultSymbolFactory() {}

    @Override
    public Symbol newSymbol(String name, int id, Symbol left, Symbol right, Object value) {
        return new Symbol(id, left, right, value);
    }

    @Override
    public Symbol newSymbol(String name, int id, Symbol left, Symbol right) {
        return new Symbol(id, left, right);
    }

    public Symbol newSymbol(String name, int id, int left, int right, Object value) {
        return new Symbol(id, left, right, value);
    }

    public Symbol newSymbol(String name, int id, int left, int right) {
        return new Symbol(id, left, right);
    }

    @Override
    public Symbol startSymbol(String name, int id, int state) {
        return new Symbol(id, state);
    }

    @Override
    public Symbol newSymbol(String name, int id) {
        return new Symbol(id);
    }

    @Override
    public Symbol newSymbol(String name, Pos pos, int id, Object value) {
        return new Symbol(id, pos, value);
    }
}
