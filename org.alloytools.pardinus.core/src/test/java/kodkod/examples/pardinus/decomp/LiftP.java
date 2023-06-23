/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.ConstantExpression;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

public final class LiftP extends DModel {

	final private int n_floors, n_states;
//	final private Variant variant;

	private final Relation state_init, state_end, state_loop, state_next, state_next_, state;
	private final Relation f_empty, f_third, f_idle, f_overload, feature, product; 
	private final Relation load, l_normal, l_empty, l_overload, l_third;
	private final Relation floor, floor_fst, floor_lst, floor_next, button_lift, button_landing;

	private final Relation button_floor, button_pressed;
	private final Relation lift_floor, lift_open, lift_up, lift_load;

	private final Relation event, event_closed, event_closed_b, event_idle, event_move, event_close, event_direction, event_pre, event_pos;

	
	private final Universe u;

	public enum Variant {
	}
	
	
	public LiftP(String[] args) {
		n_floors = Integer.valueOf(args[0]);
		n_states = Integer.valueOf(args[1]);
//		variant = Variant.valueOf(args[2]);
		
		state_init = Relation.unary("State/init");
		state_end = Relation.unary("State/end");
		state_loop = Relation.unary("State/loop");
		state_next = Relation.binary("State/next");
		state_next_ = Relation.binary("State/next_");
		state = Relation.unary("State");
		
		floor_fst = Relation.unary("Floor/init");
		floor_lst = Relation.unary("Floor/end");
		floor_next = Relation.binary("Floor/next");
		floor = Relation.unary("Floor");
		button_landing = Relation.unary("LandingButton");
		button_lift = Relation.unary("LiftButton");
		button_floor = Relation.binary("Button/floor");
		button_pressed = Relation.binary("Button/pressed");

		lift_floor = Relation.binary("Lift/floor");
		lift_open = Relation.unary("Lift/open");
		lift_up = Relation.unary("Lift/up");
		lift_load = Relation.binary("Lift/load");

		load = Relation.unary("Load");
		l_empty = Relation.unary("L_Empty");
		l_overload = Relation.unary("L_Overload");
		l_normal = Relation.unary("L_Normal");
		l_third = Relation.unary("L_Third");

		feature = Relation.unary("Feature");
		product = Relation.unary("Product");
		f_empty = Relation.unary("F_Empty");
		f_idle = Relation.unary("F_Idle");
		f_third = Relation.unary("F_Third");
		f_overload = Relation.unary("F_Overload");

		event = Relation.unary("Event");
		event_closed = Relation.unary("Closed");
		event_closed_b = Relation.binary("Closed/b");
		event_direction = Relation.unary("ChangeDir");
		event_idle = Relation.unary("IdleLift");
		event_move = Relation.unary("MoveLift");
		event_close = Relation.unary("CloseDoor");
		event_pos = Relation.binary("Event/pos");
		event_pre = Relation.binary("Event/pre");

		final List<String> atoms = new ArrayList<String>(3*n_floors + 2*n_states + 7);
		for(int i = 0; i < n_floors; i++) 
			atoms.add("Floor"+i);
		for(int i = 0; i < n_floors; i++) 
			atoms.add("LiftButton"+i);
		for(int i = 0; i < n_floors; i++) 
			atoms.add("LandingButton"+i);
		for(int i = 0; i < n_states; i++) 
			atoms.add("State"+i);
		for(int i = 0; i < n_states; i++) 
			atoms.add("Event"+i);
		atoms.add("F_Empty");
		atoms.add("F_Idle");
		atoms.add("F_Third");
		atoms.add("F_Overload");

		atoms.add("L_Normal");
		atoms.add("L_Empty");
		atoms.add("L_Third");
		atoms.add("L_Overload");

		u = new Universe(atoms);
	}

	@Override
	public PardinusBounds bounds1() {
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		final TupleSet fb = f.range(f.tuple("Floor0"), f.tuple("Floor"+ (n_floors-1)));
		final TupleSet ib = f.range(f.tuple("LiftButton0"), f.tuple("LiftButton"+ (n_floors-1)));
		final TupleSet ab = f.range(f.tuple("LandingButton0"), f.tuple("LandingButton"+ (n_floors-1)));
		final TupleSet lb = f.range(f.tuple("L_Normal"), f.tuple("L_Overload"));

		TupleSet bb = f.noneOf(2);
		for(int i = 0; i < n_floors; i++) {
			bb.add(f.tuple("LiftButton"+i,"Floor"+i));
			bb.add(f.tuple("LandingButton"+i,"Floor"+i));
		}

		b.boundExactly(floor, fb);
		b.bound(floor_lst, fb);
		b.bound(floor_fst, fb);
		b.bound(floor_next, fb.product(fb));

		b.boundExactly(button_landing, ab);
		b.boundExactly(button_lift, ib);
		b.boundExactly(button_floor, bb);

		b.boundExactly(load, lb);
		b.boundExactly(l_empty, f.setOf(f.tuple("L_Empty")));
		b.boundExactly(l_overload, f.setOf(f.tuple("L_Overload")));
		b.boundExactly(l_normal, f.setOf(f.tuple("L_Normal")));
		b.boundExactly(l_third, f.setOf(f.tuple("L_Third")));
		
		final TupleSet eb = f.range(f.tuple("F_Empty"), f.tuple("F_Overload"));
		
		b.boundExactly(feature, eb);
		b.boundExactly(f_empty, f.setOf(f.tuple("F_Empty")));
		b.boundExactly(f_idle, f.setOf(f.tuple("F_Idle")));
		b.boundExactly(f_third, f.setOf(f.tuple("F_Third")));
		b.boundExactly(f_overload, f.setOf(f.tuple("F_Overload")));
		b.bound(product, eb);

		return b;	
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final TupleSet tb = f.range(f.tuple("State0"), f.tuple("State"+ (n_states-1)));
		final TupleSet eb = f.range(f.tuple("Event0"), f.tuple("Event"+ (n_states-1)));
		final TupleSet bb = f.range(f.tuple("LiftButton0"), f.tuple("LandingButton"+ (n_floors-1)));
		final TupleSet fb = f.range(f.tuple("Floor0"), f.tuple("Floor"+ (n_floors-1)));
		final TupleSet lb = f.range(f.tuple("L_Normal"), f.tuple("L_Overload"));

		b.boundExactly(state, tb);
		b.bound(state_init, tb);
		b.bound(state_end, tb);
		b.bound(state_loop, tb);
		b.bound(state_next, tb.product(tb));
		b.bound(state_next_, tb.product(tb));

		b.boundExactly(event, eb);
		b.bound(event_closed, eb);
		b.bound(event_closed_b, eb.product(bb));
		b.bound(event_direction, eb);
		b.bound(event_move, eb);
		b.bound(event_idle, eb);
		b.bound(event_close, eb);
		b.bound(event_pos, eb.product(tb));
		b.bound(event_pre, eb.product(tb));

		b.bound(button_pressed, tb.product(bb));
		b.bound(lift_floor, tb.product(fb));
		b.bound(lift_load, tb.product(lb));
		b.bound(lift_open, tb);
		b.bound(lift_up, tb);
				
		return b;	
	}

	@Override
	public Formula partition1() {
		Formula f1 = floor_next.totalOrder(floor, floor_fst, floor_lst);
		Formula f2 = product.in(feature);
		Formula f3 = button_floor.eq(button_floor);
		Formula f4 = button_landing.eq(button_landing);
		Formula f5 = button_lift.eq(button_lift);
		Formula f6 = feature.eq(feature);
		Formula f7 = f_empty.eq(f_empty);
		Formula f8 = f_idle.eq(f_idle);
		Formula f9 = f_overload.eq(f_overload);
		Formula f10 = f_third.eq(f_third);
		Formula f11 = load.eq(load);
		Formula f12 = l_empty.eq(l_empty);
		Formula f13 = l_overload.eq(l_overload);
		Formula f14 = l_normal.eq(l_normal);
		Formula f15 = l_third.eq(l_third);
		
		product.eq(f_idle);
		
		return Formula.compose(FormulaOperator.AND, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15/*, f16*/);
	}

	@Override
	public Formula partition2() {
		return Formula.compose(FormulaOperator.AND, decls2(), defEvents(), trace(), prop());
	}
	
	public Formula prop() {
		Variable s = Variable.unary("s");
		Variable s1 = Variable.unary("s'");
		Variable b = Variable.unary("b");
		Formula f1 = b.in(s.join(button_pressed)); 
		Formula f2 = (b.join(button_floor)).eq(s1.join(lift_floor)); 
		Formula f3 = s1.in(lift_open);
		Formula f4 = (f2.and(f3)).forSome(s1.oneOf(s.join(state_next.reflexiveClosure())));
		Formula p = (f1.implies(f4)).forAll(s.oneOf(state).and(b.oneOf(button_landing)));
		
// 	all s : State | LB2 in pressed.s => some s' : s.future | Lift.floor.s' = F2 && Lift in open_door.s'  
		return p.not().and(state_loop.some());
	}

	public Formula decls2() {
		Formula f1 = state_next_.totalOrder(state, state_init, state_end);
		Formula f2 = state_next.eq(state_next_.union(state_end.product(state_loop)));
		Formula f3 = event_closed.intersection(event_close).no();
		Formula f4 = event_direction.intersection(event_move).no();
		Formula f5 = event_idle.intersection(event_direction).no();
		Formula f6 = event_idle.intersection(event_move).no();
		Formula f7 = event_closed.eq(event_move.union(event_direction).union(event_idle));
		Formula f81 = event.eq(event_close.union(event_closed));
		Formula f9 = event_pre.partialFunction(event, state);
		Formula f10 = event_pos.function(event, state);
		Formula f19 = event_closed_b.in(event_closed.product(button_lift.union(button_landing)));

		Formula f11 = button_pressed.eq(button_pressed);
		Formula f12 = lift_open.eq(lift_open);
		Formula f13 = lift_up.eq(lift_up);
		Formula f14 = lift_floor.function(state, floor);
		Formula f15 = lift_load.function(state, load);

		Formula f16 = (f_empty.in(product).not()).implies(l_empty.in(state.join(lift_load)).not());
		Formula f17 = (f_overload.in(product).not()).implies(l_overload.in(state.join(lift_load)).not());
		Formula f18 = (f_third.in(product).not()).implies(l_third.in(state.join(lift_load)).not());

		return Formula.compose(FormulaOperator.AND, f1, f2, f3, f4, f5, f6, f7, f81, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19);
	}

	private Formula trace() {
		Variable s = Variable.unary("s");
		Variable e = Variable.unary("e");
		Formula f1 = (e.join(event_pre).eq(s)).and(e.join(event_pos).eq(s.join(state_next)));
		Formula trace = f1.forSome(e.oneOf(event)).forAll(s.oneOf(state));
		
		Formula f2 = state_init.join(lift_floor).eq(floor_fst);
		Formula f3 = state_init.join(button_pressed).no();
		Formula f4 = state_init.in(lift_open);
		Formula f5 = state_init.in(lift_up);
		Formula f6 = state_init.join(lift_load).eq(l_normal);
		Formula init = f2.and(f3).and(f4).and(f5).and(f6);
		
		return trace.and(init);
	}
	
	private Formula defClosedEvent() {
		Variable e = Variable.unary("e");
		Expression pre = e.join(event_pre);
		Expression pos = e.join(event_pos);
		Expression b = e.join(event_closed_b);
		
		Formula f1 = (b.intersection(pre.join(button_pressed))).no();
		Formula f2 = (pre.in(lift_open)).not();
		Formula f5 = (pos.join(lift_load)).eq(pre.join(lift_load));
		Formula f3 = (pos.join(button_pressed)).eq(pre.join(button_pressed).union(b));
		Formula f4 = (pre.join(lift_load).eq(l_empty)).implies((b.intersection(button_lift)).no());
		
		Formula f8 = Formula.compose(FormulaOperator.AND, f1, f2, f3, f4, f5);
		
		return f8.forAll(e.oneOf(event_closed));
	}
	
	private Formula defIdleEvent() {
		Variable e = Variable.unary("e");
		Expression pre = e.join(event_pre);
		Expression pos = e.join(event_pos);
		
		Formula f1 = idle(pre);
		Formula f2 = (pos.join(lift_floor)).eq(pre.join(lift_floor));
		Formula f3 = (pos.in(lift_open)).iff(pre.in(lift_open));
		Formula f4 = (pos.in(lift_up)).iff(pre.in(lift_up));

		Formula f8 = Formula.compose(FormulaOperator.AND, f1, f2, f3, f4);
		
		return f8.forAll(e.oneOf(event_idle));
	}

	private Formula defChangeDir() {
		Variable e = Variable.unary("e");
		Expression pre = e.join(event_pre);
		Expression pos = e.join(event_pos);
		
		Formula f9 = (idle(pre)).not();
		Formula f2 = (liftcall(pre).union(landingcall(pre))).no();
		Formula f7 = (pos.in(lift_up)).iff(pre.in(lift_up)).not();
		Formula f6 = (pos.in(lift_open)).iff(pre.in(lift_open));
		Formula f4 = (pos.join(lift_floor)).eq(pre.join(lift_floor));

		Formula f8 = Formula.compose(FormulaOperator.AND, f2, f4, f6, f7, f9);
		
		return f8.forAll(e.oneOf(event_direction));
	}
	
	private Formula defMoveLift() {
		Variable e = Variable.unary("e");
		Expression pre = e.join(event_pre);
		Expression pos = e.join(event_pos);
		
		Formula f2 = (liftcall(pre).union(landingcall(pre))).some();
		Formula f9 = (pos.in(lift_open)).iff(willOpen(pos));
		
		Formula f4c = pos.join(lift_floor).eq(moveLift(pre));

		Formula f7 = (pos.in(lift_up)).iff(pre.in(lift_up));

		Formula f8 = Formula.compose(FormulaOperator.AND, f2, f9, f4c, f7);
		
		return f8.forAll(e.oneOf(event_move));
	}
	
	private Formula defCloseDoor() {
		Variable e = Variable.unary("e");
		Expression pre = e.join(event_pre);
		Expression pos = e.join(event_pos);
		
		Formula f1 = (pre.in(lift_open));
		Formula f7 = (pos.in(lift_up)).iff(pre.in(lift_up));
		Formula f4 = (pos.join(lift_floor)).eq(pre.join(lift_floor));

		Formula f2a = l_overload.in(pos.join(lift_load));
		Formula f2b = pos.in(lift_open).not();
		
		Formula f2 = f2a.or(f2b);

		Formula f9 = button_floor.join(pre.join(lift_floor)).in(pos.join(button_pressed)).not();

		Expression x = (l_empty.in(pos.join(lift_load))).thenElse(button_lift, ConstantExpression.NONE);
		Formula f3 = (pre.join(button_pressed).difference(x)).in(pos.join(button_pressed));

		Formula f8 = Formula.compose(FormulaOperator.AND, f1, f2, f3, f4, f7, f9);
		
		return f8.forAll(e.oneOf(event_close));
	}
	
	private Formula defEvents() {
		return Formula.compose(FormulaOperator.AND, defChangeDir(), defCloseDoor(), defMoveLift(), defClosedEvent(), defIdleEvent());
	}
	
	/**
	 * Moves the lift if possible (i.e., not upper floor and up or lower floor and down).
	 * @param s the state
	 * @return
	 */
	private Expression moveLift(Expression s) {
		Formula f1 = s.join(lift_floor).eq(floor_lst).not().and(s.in(lift_up));
		Formula f2 = s.join(lift_floor).eq(floor_fst).not().and(s.in(lift_up).not());
		return f1.thenElse(s.join(lift_floor).join(floor_next), f2.thenElse(s.join(lift_floor).join(floor_next.transpose()), s.join(lift_floor)));
	}

	/**
	 * In base, the door opens if there is a (lift or landing) button pressed on the current floor.
	 * If the Idle feature is selected, the the door remains open when there are not buttons pressed overall (idle).
	 * If the ThirdFull feature is selected, the door will not open for landing buttons if lift third full.
	 * (some (pressed&(thirdfull=>LiftButton,univ)).floor&floor) || (idle && FIdle)
	 * @param s the state 
	 * @return
	 */
	private Formula willOpen(Expression s) {
		Expression filter = (l_third.in(s.join(lift_load))).thenElse(button_lift, ConstantExpression.UNIV); 
		Formula f1 = (s.join(button_pressed).join(button_floor).intersection(s.join(lift_floor))).intersection(filter).some();
	    Formula f2 = (f_idle.in(product).and(idle(s)));
	    return f1.or(f2);
	}

	/**
	 * 
	 * @param s
	 * @return
	 */
	private Formula idle(Expression s) {
		return s.join(button_pressed).no();
	}

	private Expression landingcall(Expression s) {
		Expression dir = (s.in(lift_up)).thenElse(floor_next, floor_next.transpose());
		Expression dir1 = (s.in(lift_up)).thenElse(floor_lst, floor_fst);
		Expression nexts = (s.join(lift_floor).eq(dir1)).thenElse(ConstantExpression.NONE,s.join(lift_floor)).join(dir.reflexiveClosure());
		Expression calls = (s.join(button_pressed).intersection(button_landing)).join(button_floor);
		return calls.intersection(nexts);
	}

	private Expression liftcall(Expression s) {
		Expression dir = (s.in(lift_up)).thenElse(floor_next, floor_next.transpose());
		Expression dir1 = (s.in(lift_up)).thenElse(floor_lst, floor_fst);
		Expression nexts = (s.join(lift_floor).eq(dir1)).thenElse(ConstantExpression.NONE,s.join(lift_floor)).join(dir.reflexiveClosure());
		Expression calls = (s.join(button_pressed).intersection(button_lift)).join(button_floor);
		return calls.intersection(nexts);
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}
	






}
