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

import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.core.DashStrings;
import ca.uwaterloo.watform.core.DashUtilFcns;

// shortens the code to import these statically
import static ca.uwaterloo.watform.core.DashFQN.*;
import static ca.uwaterloo.watform.alloyasthelper.ExprHelper.*;

import ca.uwaterloo.watform.alloyasthelper.DeclExt;
import ca.uwaterloo.watform.alloyasthelper.ExprToString;

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
            createTrans(t);
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
        return convertFQN(s);
    }
    private void createSpaceSignatures() {
        // abstract sig Statelabel {}
        d.alloyString += d.addAbstractSigSimple(DashStrings.stateLabelName);
        // Root
        //if (d.hasConcurrency() || d.getImmChildren(d.getRootName()).isEmpty())
            //d.alloyString += d.addExtendsSigSimple(d.getRootName(),DashStrings.stateLabelName);
        //else 
            d.alloyString += d.addAbstractExtendsSigSimple(d.getRootName(),DashStrings.stateLabelName);
        recurseCreateStateSpaceSigs(d.getRootName());
        d.alloyString += "\n";

        // abstract sig TransLabel {}
        d.alloyString += d.addAbstractSigSimple(DashStrings.transitionLabelName);
        // add all transitions as one sig extensions of TransLabel
        for (String t : d.getTransNames()) {
            d.alloyString += d.addOneExtendsSigSimple(fqn(t), DashStrings.transitionLabelName);
        }
        d.alloyString += "\n";

        // abstract sig Identifiers {} if this model has parameterized components
        if (d.getMaxDepthParams() != 0) {
            d.alloyString += d.addAbstractSigSimple(DashStrings.identifierName);
            for (String s: d.getAllParams())
                d.alloyString += d.addExtendsSigSimple(s, DashStrings.identifierName);
            d.alloyString += "\n";
        }
        
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
    private void recurseCreateStateSpaceSigs(String parent) {
        for (String child: d.getImmChildren(parent)) 
            if (d.isLeaf(child)) d.alloyString += d.addOneExtendsSigSimple(fqn(child),fqn(parent));
            else {
                //if (d.isAnd(parent)) 
                    //d.alloyString += d.addExtendsSigSimple(fqn(child), fqn(parent));
                //else 
                    d.alloyString += d.addAbstractExtendsSigSimple(fqn(child), fqn(parent));
                recurseCreateStateSpaceSigs(child);  
        }   
    }
    private void createSnapshotSig(){
        if (DashOptions.isElectrum) {
            // if Electrum add var sigs 
            // taken0, conf0, event0
            
            if (d.transAtThisParamDepth(0))
                d.alloyString += d.addVarSigSimple(DashStrings.takenName+"0", createVar(DashStrings.transitionLabelName));
            d.alloyString += d.addVarSigSimple(DashStrings.confName+"0", createVar(DashStrings.stateLabelName));
            if (d.hasEvents())
                d.alloyString += d.addVarSigSimple(DashStrings.eventName+"0", createVar(DashStrings.eventLabelName));
            List<ExprVar> cop;
            for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                cop = new ArrayList<ExprVar> (Collections.nCopies(i+1,createVar(DashStrings.identifierName)));
                if (d.transAtThisParamDepth(i))
                    // taken 1, etc.
                    d.alloyString += d.addVarSigSimple(
                        DashStrings.takenName+Integer.toString(i), 
                        DashUtilFcns.newListWith(cop, createVar(DashStrings.transitionLabelName)));
                    // conf 1, etc.
                d.alloyString += d.addVarSigSimple(
                    DashStrings.confName+Integer.toString(i), 
                    DashUtilFcns.newListWith(cop, createVar(DashStrings.stateLabelName)));
                // event 1, etc.
                if (d.hasEvents())
                    d.alloyString += d.addVarSigSimple(
                        DashStrings.eventName+Integer.toString(i), 
                        DashUtilFcns.newListWith(cop, createVar(DashStrings.eventLabelName)));
            }
        
            // stable: one boolean;
            if (d.hasConcurrency()) {            
                d.alloyString += d.addVarSigSimple(DashStrings.stableName, createVar(DashStrings.boolName));
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
            if (d.transAtThisParamDepth(0))
                decls.add(DeclExt.newSetDeclExt(DashStrings.takenName+"0", DashStrings.transitionLabelName));
            decls.add(DeclExt.newSetDeclExt(DashStrings.confName+"0", DashStrings.stateLabelName));
            if (d.hasEvents())
                decls.add(DeclExt.newSetDeclExt(DashStrings.eventName+"0", DashStrings.eventLabelName));
            List<String> cop;        
            for (int i = 1; i <= d.getMaxDepthParams(); i++) {
                cop = Collections.nCopies(i+1,DashStrings.identifierName);
                // taken 1, etc. 
                if (d.transAtThisParamDepth(i)) 
                    decls.add(DeclExt.newSetDeclExt(
                        DashStrings.takenName+Integer.toString(i), 
                        createArrowList(DashUtilFcns.newListWith(cop, DashStrings.transitionLabelName))));
                // conf 1, etc.
                decls.add(DeclExt.newSetDeclExt(
                    DashStrings.confName+Integer.toString(i), 
                    createArrowList(DashUtilFcns.newListWith(cop, DashStrings.stateLabelName))));
                // event 1, etc.
                if (d.hasEvents())
                    decls.add(new DeclExt(
                        DashStrings.eventName+Integer.toString(i), 
                    createArrowList(DashUtilFcns.newListWith(cop, DashStrings.eventLabelName))));
            }
            // stable: one boolean;
            if (d.hasConcurrency()) {    
                decls.add(new DeclExt(DashStrings.stableName, createOne(createVar(DashStrings.boolName))));
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
        List<Expr> body = new ArrayList<Expr>();

        
        // p3 -> p2 -> p1 -> src in s.confVar(i)
        // src does not have to be a basic state 
        /*
        body.add(createIn(paramsToXArrow(prs,convertFQN(d.getTransSrc(t))),curConf(prs.size())));
        */
        /*
        // guard_cond_t1 [s] 
        o.add(d.getTransGuard(t).convertToAlloy(d.symbolTable, curVar(), nextVar()));

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

        d.alloyString += d.addPredSimple(convertFQN(t)+DashStrings.preName, curParamsDecls(prs), body); 
        d.alloyString += "\n";
    }
    private void createTransPost(String t) {
        List<String> prs = d.getTransParams(t); 

        // tmp
        List<Expr> body = new ArrayList<Expr>();
        d.alloyString += d.addPredSimple(convertFQN(t)+DashStrings.postName,curNextParamsDecls(prs),body);
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
                // all have same param values (or prefixes) because these trans are from srcs
                // that are ances of the src of this transition
                !pre_higherpri_trans[s,pParam0,pParam1]
                !pre_higherpri_trans[s,pParam0]
                // it depends on the params of the src state not on t1's params!  ACK!!!
                // maybe it is okay because pre_ of the trans has the correct parameters (might be trans params or something user has provided)
        }
    */
    private void createTransSemantics(String t) {
        List<Expr> body = new ArrayList<Expr>();
        List<String> prs = d.getTransParams(t);
        String tfqn = convertFQN(t); // output FQN
        

        // s'.taken = s.taken + t1
        // or
        // s'.taken2 = s.taken2 + p2 -> p1 -> tfqn
        // and other takens stay the same
        List<Expr> takens = new ArrayList<Expr>();
        for (int i=0;i <= d.getMaxDepthParams(); i++) 
            if (d.transAtThisParamDepth(i))
                if (i == prs.size())
                    if (DashOptions.isElectrum) 
                         takens.add(createEquals(
                                taken(i),
                                createUnion(taken(i),paramsToXArrow(prs,tfqn))));
                    else takens.add(createEquals(
                                nextTaken(i),
                                createUnion(curTaken(i),paramsToXArrow(prs,tfqn))));
                else
                    if (DashOptions.isElectrum) takens.add(createEquals(taken(i), curTaken(i)));
                    else takens.add(createEquals(nextTaken(i), curTaken(i)));
        Expr elseExpr = createAnd(takens);

        // no trans "below" the scope of this trans with the same params can be taken
        // (other params are for other parts of state hierarchy at this depth)

        // for the rest of the non-orthogonal trans, param values don't matter

        /*
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
    */
        takens = new ArrayList<Expr>();
        for (int i=0;i <= d.getMaxDepthParams(); i++) 
            if (d.transAtThisParamDepth(i))
                if (i == prs.size())
                    if (DashOptions.isElectrum)
                        takens.add(createEquals(
                                taken(i),
                                paramsToXArrow(prs,tfqn)));
                    else takens.add(createEquals(
                                nextTaken(i),
                                paramsToXArrow(prs,tfqn)));
                else
                    if (DashOptions.isElectrum) takens.add(createEquals(taken(i), createNone())); 
                    else takens.add(createEquals(nextTaken(i), createNone())); 
        Expr firsttaken = createAnd(takens);   
        if (d.hasConcurrency())    
            body.add(
                createITE(curStableTrue(),
                    // s'.taken = t1
                    firsttaken,
                    elseExpr)
                );
        else 
            // will only have taken0 in it
            body.add(firsttaken);

        // priority
        // depends on the src of this transition
        for (String h: d.getHigherPriTrans(t)) {
            List<String> hprs = d.getTransParams(h);
            // !pre_higherpri_trans[s,p0,p1]
            // Note: all the parameter values will be the same
            // only lower priority transitions could have more parameters
            if (DashOptions.isElectrum) 
                body.add(createNot(createPredCall(convertFQN(h+DashStrings.preName),paramVars(hprs))));
            else 
                body.add(createNot(createPredCall(convertFQN(h+DashStrings.preName),curParamVars(hprs))));
        }
        

        d.alloyString += d.addPredSimple(convertFQN(t)+DashStrings.semanticsName,curNextParamsDecls(prs),body);
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
        o.add(dash.getTransGuard(t).convertToAlloy(dash.symbolTable, nextVar(), null, prs));


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
        List<Expr> body = new ArrayList<Expr>();
        d.alloyString += d.addPredSimple(convertFQN(t)+DashStrings.isEnabledAfterStepName,decls,body);
        d.alloyString += "\n";
    }

   // --------------------------------------------------------------------------------------
    /*
        pred t1[s:Snapshot,s':Snapshot,pparam0:param0,pparam1:param1,pparam2:param2,...] =
            pparam2.pparam1.pparam0.s.pre_1 and
            pparam2.pparam1.pparam0.s'.s.post_1 and
            pparam2.pparam1.pparam0.s'.s'.semantics_t1
    */        
    private void createTrans(String t) {
        // t is FQN
        // e.g. [ClientId,ServerId.,,,]
        List<String> prs = d.getTransParams(t);
        List<Expr> body = new ArrayList<Expr>();
        String tfqn = convertFQN(t); // output FQN
        
        if (DashOptions.isElectrum) {
            // pre_transName[ p0, p1, p2] -> p2.p1.p0.pre_transName
            body.add(createPredCall(tfqn + DashStrings.preName, paramVars(prs)));
            // p2.p1.p0.post_transName
            body.add(createPredCall(tfqn + DashStrings.postName, paramVars(prs)));
            // p2.p1.p0.semantics_transName
            body.add(createPredCall(tfqn + DashStrings.semanticsName, paramVars(prs)));
        } else {
            // pre_transName[s, p0, p1, p2] -> p2.p1.p0.s.pre_transName
            body.add(createPredCall(tfqn + DashStrings.preName, curParamVars(prs)));
            // p2.p1.p0.s'.s.post_transName
            body.add(createPredCall(tfqn + DashStrings.postName, curNextParamVars(prs)));
            // p2.p1.p0.s'.s.semantics_transName
            body.add(createPredCall(tfqn + DashStrings.semanticsName, curNextParamVars(prs)));
        }
        d.alloyString += d.addPredSimple(tfqn, curNextParamsDecls(prs), body);
    }

   // --------------------------------------------------------------------------------------
    /*
        pred small_step [s:Snapshot, s': Snapshot] { 
                some pparam0 : Param0 , pparam1 : Param1 ... | 
                    { // for all t’s at level i with params Param5, Param6, ...
                    (or t[s, s_next, pparam5, pparam6 ]) 
                    // loop? big-step issue?
                }
    */
    private void createSmallStep() {

        // list of FQN of transitions
        // does not have to be done in order of number of parameters b/c all disjuncted
        ArrayList<Expr> e = new ArrayList<Expr>();
        for (String t: d.getTransNames()) {
            String tfqn = convertFQN(t); // output FQN
            // p3.p2.p1.s'.s.t for parameters of this transition
            if (DashOptions.isElectrum) e.add(createPredCall(tfqn,paramVars(d.getTransParams(t))));
            else e.add(createPredCall(tfqn,curNextParamVars(d.getTransParams(t))));
        }
        List<Expr> body = new ArrayList<Expr>();
        if (d.getAllParams().isEmpty()) body.add(createOr(e));
        else body.add(createSome(paramDecls(d.getAllParams()),createOr(e)));

        //TODO add loop if all notenabled
        d.alloyString += d.addPredSimple(DashStrings.smallStepName,curNextDecls(),body);
    }



    // common decls
    private Decl curDecl() {
        return (Decl) new DeclExt(DashStrings.curName, DashStrings.snapshotName);
    }
    private Decl nextDecl() {
        return (Decl) new DeclExt(DashStrings.nextName, DashStrings.snapshotName);
    }
    private Decl paramDecl(String n) {
        return (Decl) new DeclExt(DashStrings.pName+n, n);
    }
    private List<Decl> curNextDecls() {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) {
            o.add(curDecl());
            o.add(nextDecl());
        }
        return o;
    }
    private List<Decl> paramDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        for (String n: prs) o.add(paramDecl(n));
        return o;
    }
    private List<Decl> curParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) o.add(curDecl());
        o.addAll(paramDecls(prs));
        return o;
    }
    private List<Decl> curNextParamsDecls(List<String> prs) {
        List<Decl> o = new ArrayList<Decl>();
        if (!DashOptions.isElectrum) { o.add(curDecl()); o.add(nextDecl()); }
        o.addAll(paramDecls(prs));
        return o;
    }

    // common vars
    // s
    private ExprVar curVar() {
        return createVar(DashStrings.curName);
    }
    // s'
    private ExprVar nextVar() {
        return createVar(DashStrings.nextName);
    }
    // [n1,n2,...]
    private List<Expr> paramVars(List<String> names) {
        List<Expr> o = new ArrayList<Expr>();
        for (String n: names) o.add(createVar(DashStrings.pName+n));
        return o;
    }
    private List<Expr> curParamVars(List<String> params) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.addAll(paramVars(params));
        return o;
    }
    private List<Expr> curNextParamVars(List<String> params) {
        List<Expr> o = new ArrayList<Expr>();
        o.add(curVar());
        o.add(nextVar());
        o.addAll(paramVars(params));
        return o;
    }

    private Expr taken(int size) {
        return createVar(DashStrings.takenName + size);
    }
    private Expr conf(int size) {
        return createVar(DashStrings.confName + size);
    }
    private Expr stable() {
        return createVar(DashStrings.stableName);
    }
    // s.taken5
    private Expr curTaken(int size) {
        return curJoinExpr(taken(size));
    }
    // s'.taken5
    private Expr nextTaken(int size) {
        return nextJoinExpr(taken(size));
    }
    // s.conf4
    private Expr curConf(int size) {
        return curJoinExpr(conf(size));
    }
    // s'.conf3
    private Expr nextConf(int size) {
        return nextJoinExpr(conf(size));
    }
    // s.stable == boolean/True
    private Expr curStableTrue() {
        return createEquals(stable(),createTrue());
    }
    // s.name
    private Expr curJoinExpr(Expr e) {
        return createJoin(curVar(), e);
    }
    //s'.name
    private Expr nextJoinExpr(Expr e) {
        return createJoin(nextVar(), e);
    }
    // p3 -> p2 -> p1 -> x
    private Expr paramsToXArrow(List<String> prs, String x) {
        Collections.reverse(prs);
        Expr e = createVar(x);
        for (String p: prs) {
            e = createArrow(createVar(p),e);
        }
        return e;
    }
    /*
    private Expr predJoinCurParams(String name, List<String> prs) {
        //p2.p1.p0.s.name
        Expr e = createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = createJoin(curVar(),e);
        if (prs!= null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            System.out.println("predJoinCurParams: " +prsVarList);
            Expr x = createJoinList(prsVarList);
            System.out.println("Join of prsVarList: " + x);
            return createJoinList(prsVarList) ;
        } else return e;
    }
    private Expr predJoinCurNextParams(String name, List<String> prs) {
        //p2.p1.p0.s'.s.pre_transName
        Expr e = createVar(name);
        List<Expr> prsVarList = convertParamsToVars(prs);
        if (!DashOptions.isElectrum) e = createJoin(nextVar(),createJoin(curVar(),e));
        if (prs!=null) {
            Collections.reverse(prsVarList);
            prsVarList.add(e);
            return createJoinList(prsVarList) ;
        } else return e;      
    }
    */


}

