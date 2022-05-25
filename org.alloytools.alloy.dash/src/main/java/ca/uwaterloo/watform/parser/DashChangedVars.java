package ca.uwaterloo.watform.parser;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.ast.Expr;

public class DashChangedVars {
	String name;
	String parameter;
	List<Expr> reference;
	boolean isQuantified;
	
	public DashChangedVars(String name, String parameter) {
		this.name = name;
		this.parameter = parameter;
		this.isQuantified = parameter == null ? false : true;
	}
	
	public DashChangedVars(String name, String parameter, Expr reference) {
		this.name = name;
		this.parameter = parameter;
		this.isQuantified = parameter == null ? false : true;
		this.reference = new ArrayList<Expr>();
		this.reference.add(reference);
	}
	
	public boolean isParameterized () {
		return parameter == null ? false : true;
	}
	
	public String getName () {
		return name;
	}
	
	public String getParam() {
		return parameter;
	}
	
	public void addReference (Expr ref) {
		this.reference.add(ref);
	}
	
	public List<Expr> getReferences () {
		return this.reference;
	}
	
	public boolean isRef() {
		return reference == null ? false : true;
	}
}
