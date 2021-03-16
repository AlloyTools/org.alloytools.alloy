/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.minisat.constraints.cnf;

import java.io.Serializable;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.core.Vec;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Undoable;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;
import org.sat4j.specs.Propagatable;

/**
 * @author laihem
 * @author leberre
 * 
 */
public final class Lits implements Serializable, ILits {

    private static final int DEFAULT_INIT_SIZE = 128;

    private static final long serialVersionUID = 1L;

    private boolean pool[] = new boolean[1];

    private int realnVars = 0;

    @SuppressWarnings("unchecked")
    private IVec<Propagatable>[] watches = new IVec[0];

    private int[] level = new int[0];

    private int[] trailPosition = new int[0];

    private Constr[] reason = new Constr[0];

    private int maxvarid = 0;

    @SuppressWarnings("unchecked")
    private IVec<Undoable>[] undos = new IVec[0];

    private boolean[] falsified = new boolean[0];

    public Lits() {
        init(DEFAULT_INIT_SIZE);
    }

    @SuppressWarnings({ "unchecked" })
    public void init(int nvar) {
        if (nvar < this.pool.length) {
            return;
        }
        assert nvar >= 0;
        // let some space for unused 0 indexer.
        int nvars = nvar + 1;
        boolean[] npool = new boolean[nvars];
        System.arraycopy(this.pool, 0, npool, 0, this.pool.length);
        this.pool = npool;

        int[] nlevel = new int[nvars];
        System.arraycopy(this.level, 0, nlevel, 0, this.level.length);
        this.level = nlevel;

        int[] ntrailPosition = new int[nvars];
        System.arraycopy(this.trailPosition, 0, ntrailPosition, 0,
                this.trailPosition.length);
        this.trailPosition = ntrailPosition;

        IVec<Propagatable>[] nwatches = new IVec[2 * nvars];
        System.arraycopy(this.watches, 0, nwatches, 0, this.watches.length);
        this.watches = nwatches;

        IVec<Undoable>[] nundos = new IVec[nvars];
        System.arraycopy(this.undos, 0, nundos, 0, this.undos.length);
        this.undos = nundos;

        Constr[] nreason = new Constr[nvars];
        System.arraycopy(this.reason, 0, nreason, 0, this.reason.length);
        this.reason = nreason;

        boolean[] newFalsified = new boolean[2 * nvars];
        System.arraycopy(this.falsified, 0, newFalsified, 0,
                this.falsified.length);
        this.falsified = newFalsified;
    }

    public int getFromPool(int x) {
        int var = Math.abs(x);
        if (var >= this.pool.length) {
            init(Math.max(var, this.pool.length << 1));
        }
        assert var < this.pool.length;
        if (var > this.maxvarid) {
            this.maxvarid = var;
        }
        int lit = LiteralsUtils.toInternal(x);
        assert lit > 1;
        if (!this.pool[var]) {
            this.realnVars++;
            this.pool[var] = true;
            this.watches[var << 1] = new Vec<Propagatable>();
            this.watches[var << 1 | 1] = new Vec<Propagatable>();
            this.undos[var] = new Vec<Undoable>();
            this.level[var] = -1;
            this.trailPosition[var] = -1;
            this.falsified[var << 1] = false; // because truthValue[var] is
            // UNDEFINED
            this.falsified[var << 1 | 1] = false; // because truthValue[var] is
            // UNDEFINED
        }
        return lit;
    }

    public boolean belongsToPool(int x) {
        assert x > 0;
        if (x >= this.pool.length) {
            return false;
        }
        return this.pool[x];
    }

    public void resetPool() {
        for (int i = 0; i < this.pool.length; i++) {
            if (this.pool[i]) {
                reset(i << 1);
            }
        }
        this.maxvarid = 0;
        this.realnVars = 0;
    }

    public void ensurePool(int howmany) {
        if (howmany >= this.pool.length) {
            init(Math.max(howmany, this.pool.length << 1));
        }
        if (this.maxvarid < howmany) {
            this.maxvarid = howmany;
        }
    }

    public void unassign(int lit) {
        assert this.falsified[lit] || this.falsified[lit ^ 1];
        this.falsified[lit] = false;
        this.falsified[lit ^ 1] = false;
    }

    public void satisfies(int lit) {
        assert !this.falsified[lit] && !this.falsified[lit ^ 1];
        this.falsified[lit] = false;
        this.falsified[lit ^ 1] = true;
    }

    public void forgets(int var) {
        this.falsified[var << 1] = true;
        this.falsified[var << 1 ^ 1] = true;
    }

    public boolean isSatisfied(int lit) {
        return this.falsified[lit ^ 1] && !this.falsified[lit];
    }

    public boolean isFalsified(int lit) {
        return this.falsified[lit];
    }

    public boolean isUnassigned(int lit) {
        return !this.falsified[lit] && !this.falsified[lit ^ 1];
    }

    public String valueToString(int lit) {
        if (isUnassigned(lit)) {
            return "?"; //$NON-NLS-1$
        }
        if (isSatisfied(lit)) {
            return "T"; //$NON-NLS-1$
        }
        return "F"; //$NON-NLS-1$
    }

    public int nVars() {
        // return pool.length - 1;
        return this.maxvarid;
    }

    public int not(int lit) {
        return lit ^ 1;
    }

    public static String toString(int lit) {
        return ((lit & 1) == 0 ? "" : "-") + (lit >> 1); //$NON-NLS-1$//$NON-NLS-2$
    }

    public static String toStringX(int lit) {
        return ((lit & 1) == 0 ? "+" : "-") + "x" + (lit >> 1); //$NON-NLS-1$//$NON-NLS-2$
    }

    public void reset(int lit) {
        this.watches[lit].clear();
        this.watches[lit ^ 1].clear();
        this.level[lit >> 1] = -1;
        this.trailPosition[lit >> 1] = -1;
        this.reason[lit >> 1] = null;
        this.undos[lit >> 1].clear();
        this.falsified[lit] = false;
        this.falsified[lit ^ 1] = false;
        this.pool[lit >> 1] = false;
    }

    public int getLevel(int lit) {
        return this.level[lit >> 1];
    }

    public void setLevel(int lit, int l) {
        this.level[lit >> 1] = l;
    }

    public Constr getReason(int lit) {
        return this.reason[lit >> 1];
    }

    public void setReason(int lit, Constr r) {
        this.reason[lit >> 1] = r;
    }

    public IVec<Undoable> undos(int lit) {
        return this.undos[lit >> 1];
    }

    public void watch(int lit, Propagatable c) {
        this.watches[lit].push(c);
    }

    public IVec<Propagatable> watches(int lit) {
        return this.watches[lit];
    }

    public boolean isImplied(int lit) {
        int var = lit >> 1;
        assert this.reason[var] == null || this.falsified[lit]
                || this.falsified[lit ^ 1];
        // a literal is implied if it is a unit clause, ie
        // propagated without reason at decision level 0.
        return this.pool[var]
                && (this.reason[var] != null || this.level[var] == 0);
    }

    public int realnVars() {
        return this.realnVars;
    }

    /**
     * To get the capacity of the current vocabulary.
     * 
     * @return the total number of variables that can be managed by the
     *         vocabulary.
     */
    protected int capacity() {
        return this.pool.length - 1;
    }

    /**
     * @since 2.1
     */
    public int nextFreeVarId(boolean reserve) {
        if (reserve) {
            ensurePool(this.maxvarid + 1);
            // ensure pool changes maxvarid
            return this.maxvarid;
        }
        return this.maxvarid + 1;
    }

    @Override
    public void setTrailPosition(int lit, int position) {
        this.trailPosition[lit >> 1] = position;
    }

    @Override
    public int getTrailPosition(int lit) {
        return this.trailPosition[lit >> 1];
    }
}
