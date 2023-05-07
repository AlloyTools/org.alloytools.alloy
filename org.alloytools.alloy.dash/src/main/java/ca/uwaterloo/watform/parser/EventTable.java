package ca.uwaterloo.watform.parser;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Collections;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprVar;

import static ca.uwaterloo.watform.core.DashUtilFcns.*;
import static ca.uwaterloo.watform.core.DashStrings.*;
import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashFQN;
import ca.uwaterloo.watform.core.DashRef;

import ca.uwaterloo.watform.alloyasthelper.ExprHelper;

public class EventTable {

	// stores Event Decls in a HashMap based on the event FQN

	private HashMap<String,EventElement> table;


	public class EventElement {
		private IntEnvKind kind;
		private List<String> params;

		public EventElement(
			IntEnvKind k,
			List<String> prms) {
			assert(prms != null);
			this.kind = k;
			this.params = prms;
		}
		public String toString() {
			String s = new String();
			s += "kind: "+kind+"\n";
			s += "params: "+ NoneStringIfNeeded(params) +"\n";
			return s;
		}
	}

	public EventTable() {
		this.table = new HashMap<String,EventElement>();

	}
	public String toString() {
		String s = new String("EVENT TABLE\n");
		for (String k:table.keySet()) {
			s += " ----- \n";
			s += k + "\n";
			s += table.get(k).toString();
		}
		return s;
	}	
	public Boolean add(String efqn, IntEnvKind k, List<String> prms) {
		assert(prms!=null);
		if (table.containsKey(efqn)) return false;
		else if (hasPrime(efqn)) { DashErrors.nameShouldNotBePrimed(efqn); return false; }
		else { table.put(efqn, new EventElement(k,prms)); return true; }
	}
	public void resolveAllEventTable() {
		// TODO
	}
	public boolean hasEvents() {
		return (!table.keySet().isEmpty() );
	}
	public boolean hasEvent(String e) {
		return table.containsKey(e);
	}
	public boolean hasEventsAti(int i) {
		for (String e: table.keySet()) {
			if (table.get(e).params.size() == i) return true;
		}
		return false;	
	}
	public boolean hasInternalEvents() {
		for (String e: table.keySet()) {
			if (table.get(e).kind == IntEnvKind.INT) return true;
		}
		return false;
	}
	public boolean hasEnvironmentalEvents() {
		for (String e: table.keySet()) {
			if (table.get(e).kind == IntEnvKind.ENV) return true;
		}
		return false;
	}
	public List<String> getAllInternalEvents() {
		return table.keySet().stream()
			.filter(i -> table.get(i).kind == IntEnvKind.INT)
			.collect(Collectors.toList());	
	}
	public List<String> getAllEnvironmentalEvents() {
		return table.keySet().stream()
			.filter(i -> table.get(i).kind == IntEnvKind.ENV)
			.collect(Collectors.toList());	
	}
	public List<String> getAllEventNames() {
		return new ArrayList<String>(table.keySet());
	}
	public List<String> getParams(String efqn) {
		if (table.containsKey(efqn)) return table.get(efqn).params;
		else { DashErrors.eventTableEventNotFound("getParams", efqn); return null; }
	}
	public boolean isEnvironmentalEvent(String efqn) {
		if (table.containsKey(efqn)) return (table.get(efqn).kind == IntEnvKind.ENV);
		else { DashErrors.eventTableEventNotFound("isEnvironmentalEvent", efqn); return false; }	
	}
	public List<String> allEventsOfState(String sfqn) {
		// return all events declared in this state
		// will have the sfqn as a prefix
		return table.keySet().stream()
			.filter(i -> DashFQN.chopPrefixFromFQN(i).equals(sfqn))
			.collect(Collectors.toList());	
	}

	public DashRef resolveEvent(String xType, Expr exp, List<String> region, String tfqn, List<String> tparams, VarTable vt) {


		// don't include isDashRefJoin here because that is only possible for actions not events
		// which are tuples
		// but a DashRefProcessRef could be either a value for an action
		// or a tuple for an event
		// Arrow: b1 -> a1 -> ev
		// ProcessRef: A/B/C[a1,b1]/ev which became $$PROCESSREF$$. b1.a1.A/B/C/ev in parsing
		// BadJoin: ev[a1,b1] which became b1.a1.ev in parsing 
		if (ExprHelper.isExprVar(exp) ||
			//DashRef.isDashRefArrow(exp) || 
			DashRef.isDashRefProcessRef(exp))// || 
			//DashRef.isDashRefBadJoin(exp)) 
		{
			String e;
			List<Expr> paramValues;
			if (ExprHelper.isExprVar(exp)) {
				e = ExprHelper.getVarName((ExprVar) exp);	
				paramValues = new ArrayList<Expr>();
			} else {
				e = DashRef.nameOfDashRefExpr(exp);
				paramValues = 
					// have to recursive through expressions in parameters
					DashRef.paramValuesOfDashRefExpr(exp).stream()
						.map(i -> vt.resolveExpr(xType, i, region, tfqn, tparams))
						.collect(Collectors.toList());
			}
			String efqn = DashFQN.fqn(e);

			//System.out.println(efqn);
			List<String> matches = new ArrayList<String>();
			if (paramValues.isEmpty()) {
				// if no param values must be within the region of the same params (could be prefix of params)
				for (String s:region) 
					for (String x:allEventsOfState(s)) {
						if (DashFQN.suffix(x,efqn)) matches.add(x);
					}
			} else {
				// if it has params values, could be suffix of any event
				// and later we check it has the right number of params
				for (String x:getAllEventNames()) {
					if (DashFQN.suffix(x,efqn)) matches.add(x);
				}		
			}

			if (matches.size() > 1) {
				DashErrors.ambiguousEvent(xType, e, tfqn);
				return null; 
			} else if (matches.isEmpty()) {
				DashErrors.unknownEvent(xType, e,tfqn);
				return null;
			} else {
				String m = matches.get(0);	
				if (paramValues.isEmpty()) {
					// must have same param values as trans b/c in same conc region
					if (getParams(m).size() > tparams.size()) {
						// getRegion did not return things that all
						// have the same parameter values
						DashErrors.regionMatchesWrongParamNumber();
						return null;
					} else {
						// but could be a subset of transition param values
						List<Expr> prmValues = 
							ExprHelper.createVarList(pName,
								tparams.subList(0, getParams(m).size() ));
						return new DashRef(m, prmValues);							
					}
				} else if (getParams(m).size() != paramValues.size()) { 
					// came with parameters so must be right number
					DashErrors.fqnEventMissingParameters(xType, e, tfqn); 
					return null;
				} else {
					return new DashRef(m,paramValues); 
				}
			}
		} else {
			DashErrors.expNotEvent(xType, tfqn);
			return null;
		}
		
	}

}