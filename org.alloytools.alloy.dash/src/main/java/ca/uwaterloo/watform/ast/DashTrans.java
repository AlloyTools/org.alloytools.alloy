package ca.uwaterloo.watform.ast;

import java.util.List;
import java.util.ArrayList;
import java.util.StringJoiner;
import java.util.Collections;
import java.util.stream.Collectors;

import ca.uwaterloo.watform.core.*;

import ca.uwaterloo.watform.parser.StateTable;
import ca.uwaterloo.watform.parser.TransTable;

import edu.mit.csail.sdg.alloy4.Pos;

public class DashTrans extends Dash {
	String name;
	List<Object> items;

	public DashTrans(Pos p,String n, List<Object> i) {
		assert(n != null && i != null);
		this.pos = p;
		this.name = n;
		this.items = i;
	}

	public String toString() {
		String s = new String("");
		if (items.isEmpty()) {
			s += DashStrings.transName + " " + name + " { }\n";
		} else { 
		    s += DashStrings.transName + " " + name + " {\n";
			StringJoiner j = new StringJoiner("");
 			items.forEach(i -> j.add(i.toString()));
			s += j.toString() + "}\n";
		}
		return s;
	}
	public void load(TransTable tt, List<String> params, List<Integer> paramsIdx, List<String> ances) {

		if (DashFQN.isFQN(name)) DashErrors.transNameCantBeFQN(pos, name);
		String tfqn = DashFQN.fqn(ances,name);
		//System.out.println("HERE3 "+items.toString());
		List<Object> xItems = new ArrayList<Object>(items);
		//System.out.println("HERE3 "+xItems.toString());
		List<DashFrom> fromList = 
			xItems.stream()
			.filter(i -> i instanceof DashFrom)
			.map(i -> (DashFrom) i)
			.collect(Collectors.toList());
		xItems.removeAll(fromList);

		List<DashOn> onList =
			xItems.stream()
			.filter(i -> i instanceof DashOn)
			.map(i -> (DashOn) i)
			.collect(Collectors.toList());	

		xItems.removeAll(onList);

		List<DashWhen> whenList =
			xItems.stream()
			.filter(i -> i instanceof DashWhen)
			.map(i -> (DashWhen) i)
			.collect(Collectors.toList());	
		xItems.removeAll(whenList);

		List<DashGoto> gotoList = 
			xItems.stream()
			.filter(i -> i instanceof DashGoto)
			.map(i -> (DashGoto) i)
			.collect(Collectors.toList());
		xItems.removeAll(gotoList);

		List<DashSend> sendList =
			xItems.stream()
			.filter(i -> i instanceof DashSend)
			.map(i -> (DashSend) i)
			.collect(Collectors.toList());	
		xItems.removeAll(sendList);

		List<DashDo> doList =
			xItems.stream()
			.filter(i -> i instanceof DashDo)
			.map(i -> (DashDo) i)
			.collect(Collectors.toList());	
		xItems.removeAll(doList);

		if (!tt.add(tfqn,params, paramsIdx, fromList, onList, whenList, gotoList, sendList, doList)) DashErrors.dupTransNames(pos,name);
		//System.out.println(xItems);
		if (!xItems.isEmpty()) DashErrors.nonEmptyTransItems();
	}
}