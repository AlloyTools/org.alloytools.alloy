package org.sat4j.minisat.orders;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.PrintWriter;
import java.util.Scanner;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.specs.IVecInt;

/**
 * Forces the order of the heuristics for some literals. Then hand back to a
 * dynamic heuristics.
 * 
 * @author leberre
 *
 */
@Feature(value = "varheuristics", parent = "expert")
public class OrientedOrder implements IOrder {

    private final IVecInt orderedLits = new VecInt();
    private boolean[] managed;
    private ILits voc;

    private final String fileName;

    private final IOrder order;

    public OrientedOrder(String fileName, IOrder order) {
        this.fileName = fileName;
        this.order = order;
    }

    @Override
    public void setLits(ILits lits) {
        order.setLits(lits);
        voc = lits;
    }

    @Override
    public int select() {
        int p;
        for (int i = 0; i < orderedLits.size(); i++) {
            p = orderedLits.get(i);
            if (voc.isUnassigned(p)) {
                return p;
            }
        }
        return order.select();
    }

    @Override
    public void undo(int x) {
        if (!managed[x >> 1]) {
            order.undo(x);
        }
    }

    @Override
    public void updateVar(int p) {
        if (!managed[p >> 1]) {
            order.updateVar(p);
        }
    }

    @Override
    public void updateVar(int p, double value) {
        updateVar(p);
    }

    @Override
    public void init() {
        order.init();
        managed = new boolean[voc.nVars() + 1];
        try (Scanner in = new Scanner(
                new BufferedReader(new FileReader(fileName)))) {
            while (in.hasNext()) {
                append(in.nextInt());
            }
        } catch (FileNotFoundException e) {
            throw new IllegalStateException(e);
        }
    }

    private void append(int l) {
        int p = LiteralsUtils.toInternal(l);
        orderedLits.push(p);
        managed[p >> 1] = true;
    }

    @Override
    public void printStat(PrintWriter out, String prefix) {
        order.printStat(out, prefix);
    }

    @Override
    public void setVarDecay(double d) {
        order.setVarDecay(d);
    }

    @Override
    public void varDecayActivity() {
        order.varDecayActivity();
    }

    @Override
    public double varActivity(int p) {
        return order.varActivity(p);
    }

    @Override
    public void assignLiteral(int p) {
        if (!managed[p >> 1]) {
            order.assignLiteral(p);
        }
    }

    @Override
    public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
        order.setPhaseSelectionStrategy(strategy);
    }

    @Override
    public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
        return order.getPhaseSelectionStrategy();
    }

    @Override
    public void updateVarAtDecisionLevel(int q) {
        if (!managed[q >> 1]) {
            order.updateVarAtDecisionLevel(q);
        }
    }

    @Override
    public double[] getVariableHeuristics() {
        return order.getVariableHeuristics();
    }

}
