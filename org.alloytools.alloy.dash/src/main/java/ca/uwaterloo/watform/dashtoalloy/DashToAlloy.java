/*
 * Functions for translating Dash to Alloy
 * The translation is done in place so the Dash
 * module contains the original "state" and its 
 * translation to Alloy but there
 * is too much code to put this all in one file
 */

package ca.uwaterloo.watform.dashtoalloy;

import java.util.Collections;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;

import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Expr;
import ca.uwaterloo.watform.core.*;


import ca.uwaterloo.watform.alloyasthelper.*;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.CompModuleHelper;

public class DashToAlloy {
	private DashModule d;

    public DashToAlloy(DashModule dash) {
        this.d = dash;
    }

    public void translate() {
        assert(d.hasRoot());
        // translation is done in place
        createSpaceSignatures();  // state, transition, parameter, buffer space
        createSnapshotSig();
        for (String t: d.getTransNames()) {
            createTransPre(t);
            createTransPost(t);
            createTransSemantics(t);
            createTransIsEnabledAfterStep(t);
            createTransPred(t);
        }
        createSmallStep();
    }

    // make it shorter internally
    private String fqn(String s) {
        // internally we use "/" to separate FQN parts
        // because Alloy names might use "_"
        // but we can't output "/" in Alloy identifiers
        // so before outputting we convert "/" to "_"
        // for everything
        return DashFQN.convertFQN(s);
    }
    private void createSpaceSignatures() {
        // abstract sig Statelabel
        d.alloyString += d.addAbstractSigSimple(DashStrings.stateLabelName);
        // abstract sig SystemState extend StateLabel
        d.alloyString += d.addAbstractExtendsSigSimple(DashStrings.systemStateName,DashStrings.stateLabelName);

        recurseCreateStateSpaceSigs(DashStrings.stateLabelName, fqn(d.getRootName()));

        d.alloyString += "\n";

        d.alloyString += d.addAbstractSigSimple(DashStrings.transitionLabelName);
        for (String t : d.getTransNames()) {
            d.alloyString += d.addOneExtendsSigSimple(fqn(t), DashStrings.transitionLabelName);
        }
        d.alloyString += "\n";
        if (d.getMaxDepthParams() != 0) d.alloyString += d.addAbstractSigSimple(DashStrings.identifierName);
        if (!d.getAllParams().isEmpty())
            for (String s: d.getAllParams())
                d.alloyString += d.addExtendsSigSimple(s, DashStrings.identifierName);
        d.alloyString += "\n";
        /*
        if (d.hasEvents()) {
            addAbstractSigSimple(eventLabelName);
            if (d.hasInternalEvents()) {
                addAbstractExtendsSigSimple( environmentEventName, eventLabelName);
                    for (e: d.getInternalEventNames()) {
                        addOneExtendsSigSimple(e,internalEventName)
                    }
            } 
            if (d.hasExternalEvents()){
                addAbstractExtendsSigSimple( internalEventName, eventLabelName);
                for (e: d.getExternalEventNames()) {
                    addOneExtendsSigSimple(e,internalEventName)
                }
            }
        }


    
        if (d.hasBuffers()) {
            for (String i: d.getBufferIndices()) {
                addSigSimple( i);
            }
        } 
        */
    }
    private void recurseCreateStateSpaceSigs(String parent, String child) {
        if (d.isBasicState(child)) d.alloyString += d.addOneExtendsSigSimple(fqn(child),fqn(parent));
        else {
            d.alloyString += d.addAbstractExtendsSigSimple(fqn(child), fqn(parent));
            for (String grandchild: d.getImmChildren(child)) recurseCreateStateSpaceSigs(child, grandchild);
        }   
    }
    private void createSnapshotSig(){
        if (DashOptions.isElectrum) {
            // if Electrum add var sigs 
            // taken0, conf0, event0
            d.alloyString += d.addVarSigSimple(DashStrings.takenName+"0", ExprHelper.createVar(DashStrings.transitionLabelName));
            d.alloyString += d.addVarSigSimple(DashStrings.confName+"0", ExprHelper.createVar(DashStrings.stateLabelName));
            if (d.hasEvents())
                d.alloyString += d.addVarSigSimple(DashStrings.eventName+"0", ExprHelper.createVar(DashStrings.eventLabelName));
            if (d.getMaxDepthParams() != 0) {
                for (int i = 1; i < d.getMaxDepthParams()+1; i++) {
                    List<ExprVar> cop = new ArrayList<ExprVar> (Collections.nCopies(i,ExprHelper.createVar(DashStrings.identifierName)));
                    // taken 1, etc.
                    d.alloyString += d.addVarSigSimple(
                        DashStrings.takenName+Integer.toString(i), 
                        DashUtilFcns.newListWith(cop, ExprHelper.createVar(DashStrings.transitionLabelName)));
                    // conf 1, etc.
                    d.alloyString += d.addVarSigSimple(
                        DashStrings.confName+Integer.toString(i), 
                        DashUtilFcns.newListWith(cop, ExprHelper.createVar(DashStrings.stateLabelName)));
                    // event 1, etc.
                    if (d.hasEvents())
                        d.alloyString += d.addVarSigSimple(
                            DashStrings.eventName+Integer.toString(i), 
                            DashUtilFcns.newListWith(cop, ExprHelper.createVar(DashStrings.eventLabelName)));
                }
            }
            // stable: one boolean;
            if (d.hasConcurrency()) {            
                //TODO now to make this one boolean
                d.alloyString += d.addVarSigSimple(DashStrings.stableName, ExprHelper.createVar(DashStrings.boolName));
            }
            // add dynamic symbols (vars and buffers)
            /*
            for (DashDynSymbols v: getDynSymbols()) {
                List<String> prms = Collections.nCopies(DashStrings.IdentifiersName, v.getParams().size());
                addVarSigSimple(
                    v.getFullyQualName(), 
                    createArrowList(prms+v.createAlloyTyp()));
            }    
            */
        } else {
            // if traces/tcmc sig Snapshot {} with fields
            List<Decl> decls = new ArrayList<Decl>();

            // taken0, conf0, event0
            decls.add(DeclExt.newSetDeclExt(DashStrings.takenName+"0", DashStrings.transitionLabelName));
            decls.add(DeclExt.newSetDeclExt(DashStrings.confName+"0", DashStrings.stateLabelName));
            if (d.hasEvents())
                decls.add(DeclExt.newSetDeclExt(DashStrings.eventName+"0", DashStrings.eventLabelName));
            if (d.getMaxDepthParams() != 0) {
                for (int i = 1; i < d.getMaxDepthParams()+1; i++) {
                    List<String> cop = Collections.nCopies(i+1,DashStrings.identifierName);
                    // taken 1, etc. 
                    decls.add(DeclExt.newSetDeclExt(
                        DashStrings.takenName+Integer.toString(i), 
                        ExprHelper.createArrowList(DashUtilFcns.newListWith(cop, DashStrings.transitionLabelName))));
                    // conf 1, etc.
                    decls.add(DeclExt.newSetDeclExt(
                        DashStrings.confName+Integer.toString(i), 
                        ExprHelper.createArrowList(DashUtilFcns.newListWith(cop, DashStrings.stateLabelName))));
                    // event 1, etc.
                    if (d.hasEvents())
                        decls.add(new DeclExt(
                            DashStrings.eventName+Integer.toString(i), 
                        ExprHelper.createArrowList(DashUtilFcns.newListWith(cop, DashStrings.eventLabelName))));
                }
            }
            // stable: one boolean;
            if (d.hasConcurrency()) {    
                decls.add(new DeclExt(DashStrings.stableName, ExprHelper.createOne(ExprHelper.createVar(DashStrings.boolName))));
            }
            // add dynamic symbols (vars and buffers)
            /*
            for (DashDynSymbols v: getDynSymbols()) {
                List<String> prms = Collections.nCopies(DashStrings.IdentifiersName, v.getParams().size());
                decls.add(createDecl(
                    v.getFullyQualName(), 
                    createArrowList(prms+v.createAlloyTyp())));
            }
            */

            d.alloyString += d.addSigWithDeclsSimple( DashStrings.snapshotName, decls);
        }
        d.alloyString += "\n";
    }
        // --------------------------------------------------------------------------------------
    /* 
        pred pre_t1[s:Snapshot,pparam0:Param0, ...] {
            src_state_t1 in <prs for src_state>.s.conf 
            guard_cond_t1 [s] 
            s.stable = True => 
                { // beginning of a big step 
                  // transition can be triggered only by environmental events 
                  <prs for trig_event>.trig_events_t1 in (s.events & EnvironmentalEvent ) 
                } else { 
                  // intermediate snapshot 
                  // transition can be triggered by any type of event 
                  <prs for trig_event>.trig_events_t1 in s.events 
                }
        }
        Assumption: prs for src state and trig events are a subset of prs for trans
    */
    private void createTransPre(String t) {
        List<String> prs = d.getTransParams(t); 
        List<Expr> o = new ArrayList<Expr>();

        /*
        // p3 -> p2 -> p1 -> src in s.confVar(i)
        // src does not have to be a basic state 
        Expr src = createVar(d.getTransSrc(t));
        ArrayList<Expr> psList = createVars(prs);       
        o.add(createIn(createArrowList(createVars(prs).add(src)),curConf(prs.size())));

        // guard_cond_t1 [s] 
        o.add(d.getTransGuard(t).convertToAlloy(d.symbolTable, sCurVar(), sNextVar()));

        // events
        if (d.hasConcurrency() && d.getTransTrigger(t) != null && d.hasEnvironmentalEvents()) {
            // trig_events_t1
            ArrayList<Expr> trigEvents = new ArrayList<Expr>();
            for (e:d.getTransTriggerEvents(t)) {
                // p3 -> p2 -> p1 -> event
                trigEvents.add(createArrowList(createVars(d.getEventParams(e)).add(createVar(e))));
            }
            Expr te = createPlus(trigEvents);
            o.add(createITE(
                createEquals(curStable(),createTrue())
                // have to look at different levels!!
                createIn(te, createAnd(curEvents(),createVar(DashStrings.environmentEventName))),
                createIn(te, curEvents()))
            );
        }
        Expr body = createAnd(o);
        */

        // tmp
        List<Expr> body = Arrays.asList(ExprHelper.createNullExpr());

        d.alloyString += d.addPredSimple(DashFQN.convertFQN(t)+DashStrings.preName, curParamsDecls(prs), body); 
        d.alloyString += "\n";
    }
    private void createTransPost(String t) {
        List<String> prs = d.getTransParams(t); 

        // tmp
        List<Expr> body = Arrays.asList(ExprHelper.createNullExpr());
        d.alloyString += d.addPredSimple(DashFQN.convertFQN(t)+DashStrings.postName,curNextParamsDecls(prs),body);
    }
    // -----------------------------------------------------------------------------
    /*
        pred t1_semantics[s:Snapshot,s':Snapshot, pParam0: Param0, ... ] {
            (s.stable = True) => {
                s'.taken = t1      
            } else {
                s'.taken = s.taken + t1
                no t1.notOrthogonal & (s.taken0 + taken0 |> TransitionLabel + s.taken1 |> TransitionLabel + ...)
            }
            for all t in t1.higherPri 
                some p0. p1. !pre_higherpri_trans[s,p0,p1]
        }
    */
    private void createTransSemantics(String t) {
        //List<Expr> body = new ArrayList<Expr>();
        List<String> prs = d.getTransParams(t);

        /*
        // s'.taken = s.taken + t1
        Expr elseExpr = createEquals(nextTaken(prs.size()),createPlus(curTaken(prs.size()),createParamsJoin(prs,t1)));
        if (notOrthogonal != null) {
            elseExpr = 
                createAnd(
                    elseExpr, 
                    // no t1.notOrthogonal & (s.taken + s.taken1 |> TransitionLabel + taken2 |> TransitionLabel + ...)  
                    createNo(
                        createAnd(
                            createNonOrthogonalExpr(t),
                            createChoppedGroup(prs.size(),DashStrings.takenName,DashStrings.transitionLabelName))));
        }     

        body.add(
            createITE(sCurStableTrue(),
                // s'.taken = t1
                createEquals(nextTaken(prs.size()), createParamsJoin(prs,t1)),
                elseExpr
            )
        for (h: dash.transTable.get(t).getHigherPriority()) {
            List<String> prs = h.getParams();
            // some p0. p1. !pre_higherpri_trans[s,p0,p1]
            body.add(createSome(paramsDecls(prs), createNot(curJoinParams(prs,h+DashStrings.preName))))
        }
        */
        // tmp
        List<Expr> body = Arrays.asList(ExprHelper.createNullExpr());
        d.alloyString += d.addPredSimple(DashFQN.convertFQN(t)+DashStrings.semanticsName,curNextParamsDecls(prs),body);
        d.alloyString += "\n";
    }
    // ---------------------------------------------------
    /*
    // this is considering all instances of t1s (thus, the existential quantification)
    pred t1_enabledAfterStep[
            s:Snapshot,s':Snapshot,  
            pParam0: Param0, ...
            t:TransitionLabel, // parameters don't matter for orthogonality
            ge:EventLabel ] 
    {   // b/c below is exists params, the params don't matter
        src_state_t1 in s'.confi // where i is depth of src_state, 
        guard_cond_t1[s'] // may depend on params
        (s.stable = True) =>
            no t1.notOrthogonal & t 
            for all of t1's triggering events and forall n
                (if trig_ev_t1 is internal, line below is false)
                trig_ev_t1  in (chop0(s.event0,EnvEvents) + chop1(s.event1,EnvEvents) + chop2(s.event2,EnvEvents) ... + ge)
        else {
            no t1.notOrthogonal & (t + s.taken0 + s.taken1.TransLabel + s.taken2.TransLabel + s.taken3.TransLabel ...)
            for all of t1's triggering events and forall n
                trig_ev_t1  in (s.event0.EventLabel + s.event1.EventLabel + s.event2.EventLabel ... + ge)     
        }
    }
    */
    private void createTransIsEnabledAfterStep(String t) {
        List<String> prs = d.getTransParams(t); 
        /*
        ArrayList<Expr> o = new ArrayList<Expr>();

        
        // src does not have to be a basic state 
        Expr src = createVar(dash.getTransSrc(t));
        ArrayList<Expr> psList = createVars(prs); 
        List<String> trig_ev = dash.transTable.get(t).getWhen();
        List<String> int_trig_ev = trig_ev.stream().filter(ev -> ev.isInternal()).collect(Collectors.toList());

        // p3 -> p2 -> p1 -> src in s'.confVar(i)    
        o.add(createIn(createArrowList(createVars(prs).add(src)),nextConf(prs.size())));

        // guard_cond_t1 [s'] 
        // final parameter (usually s') should not be used in precondition
        o.add(dash.getTransGuard(t).convertToAlloy(dash.symbolTable, sNextVar(), null, prs));


        // no t1.notOrthogonal & (t + s.taken + s.taken1 |> TransitionLabel + taken2 |> TransitionLabel + ...)  
        Expr elseExpr = createNo(
            createAnd(
                createNonOrthogonalExpr(t),createPlus(createVar(t), 
                createChoppedGroup(prs.size(),DashStrings.takenName,DashStrings.transitionLabelName))));
        elseExpr = createAnd(
            elseExpr,
            createIn(
                createPlusList(createVarList(trig_ev)),
                createPlus(
                    // chop(s.event0,EventLabel + chop(s.event1,EventLabel) + chop(s.event2,EventLabel) 
                    createChoppedGroup(prs.size(),DashStrings.eventName,DashStrings.eventLabelName),
                    ge)));

        if (int_trig_ev == null) {
            // no t1.notOrthogonal & t 
            Expr ifExpr = createNo(createAnd(createNonOrthogonalExpr(t),createVar(t)));
            ifExpr = createAnd(
                ifExpr,
                createIn(
                    createPlusList(createVarList(trig_ev)),
                    // chop(s.event0,EnvEvents) + chop1(s.event1,EnvEvents) + chop2(s.event2,EnvEvents)
                    createPlus(createChoppedGroup(prs.size(),DashStrings.eventName,DashStrings.environmentEventName),ge)))
            body.add(createITE(sStableTrue(),ifExpr,elseExpr));
        } else {
            body.add(createITE(sStableTrue(),createFalse(),elseExpr));
        }
        */
        List<Decl> decls = curNextParamsDecls(prs);
        decls.add((Decl) new DeclExt(DashStrings.tName, DashStrings.transitionLabelName));
        if (d.hasEvents())
            decls.add((Decl) DeclExt.newSetDeclExt(DashStrings.geName, DashStrings.eventLabelName));
        // tmp
        List<Expr> body = Arrays.asList(ExprHelper.createNullExpr());
        d.alloyString += d.addPredSimple(DashFQN.convertFQN(t)+DashStrings.isEnabledAfterStepName,decls,body);
        d.alloyString += "\n";
    }

   // --------------------------------------------------------------------------------------
    /*
        pred t1[s:Snapshot,s':Snapshot,pparam0:param0,pparam1:param1,pparam2:param2,...] =
            pparam2.pparam1.pparam0.s.pre_1 and
            pparam2.pparam1.pparam0.s'.s.post_1 and
            pparam2.pparam1.pparam0.s'.s'.semantics_t1
    */        
    private void createTransPred(String t) {
        // t is FQN
        // e.g. [ClientId,ServerId.,,,]
        List<String> prs = d.getTransParams(t);
        List<Expr> body = new ArrayList<Expr>();
        String tfqn = DashFQN.convertFQN(t);
        // pre_transName[s, p0, p1, p2] -> p2.p1.p0.s.pre_transName
        body.add(ExprHelper.createPredCall(tfqn + DashStrings.preName, curParamsArgs(prs)));
        // p2.p1.p0.s'.s.post_transName
        body.add(ExprHelper.createPredCall(tfqn + DashStrings.preName, curNextParamsArgs(prs)));
        // p2.p1.p0.s'.s.semantics_transName
        body.add(ExprHelper.createPredCall(tfqn + DashStrings.preName, curNextParamsArgs(prs)));
        d.alloyString += d.addPredSimple(tfqn, curNextParamsDecls(prs), body);
        d.alloyString += "\n";
    }

    private void createSmallStep() {
        ;
    }

    // useful shortcuts 
    private Decl sCurDecl() {
        return (Decl) new DeclExt(DashStrings.sCurName, DashStrings.snapshotName);
    }
    private Decl sNextDecl() {
        return (Decl) new DeclExt(DashStrings.sNextName, DashStrings.snapshotName);
    }
    private Decl paramDecls(String n) {
        return (Decl) new DeclExt(DashStrings.pName+n, n);
    }
    private List<Decl> curParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) o.add(sCurDecl());
        for (String n: prs) o.add(paramDecls(n));
        return o;
    }
    private List<Decl> curNextParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) { o.add(sCurDecl()); o.add(sNextDecl()); }
        for (String n: prs) o.add(paramDecls(n));
        return o;
    }

    private ExprVar sCurVar() {
        return ExprHelper.createVar(DashStrings.sCurName);
    }
    private ExprVar sNextVar() {
        return ExprHelper.createVar(DashStrings.sNextName);
    }
    private List<Expr> convertParamsToVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(ExprHelper.createVar(DashStrings.pName+n));
        return o;
    }
    private List<Expr> curParamsArgs(List<String> params) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(sCurVar());
        o.addAll(convertParamsToVars(params));
        return o;
    }
    private List<Expr> curNextParamsArgs(List<String> params) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(sCurVar());
        o.add(sNextVar());
        o.addAll(convertParamsToVars(params));
        return o;
    }
    /*
    private Expr predJoinCurParams(String name, List<String> prs) {
        //p2.p1.p0.s.name
        Expr e = ExprHelper.createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = ExprHelper.createJoin(sCurVar(),e);
        if (prs!= null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            System.out.println("predJoinCurParams: " +prsVarList);
            Expr x = ExprHelper.createJoinList(prsVarList);
            System.out.println("Join of prsVarList: " + x);
            return ExprHelper.createJoinList(prsVarList) ;
        } else return e;
    }
    private Expr predJoinCurNextParams(String name, List<String> prs) {
        //p2.p1.p0.s'.s.pre_transName
        Expr e = ExprHelper.createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = ExprHelper.createJoin(sNextVar(),ExprHelper.createJoin(sCurVar(),e));
        if (prs!=null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            return ExprHelper.createJoinList(prsVarList) ;
        } else return e;      
    }
    */


}

