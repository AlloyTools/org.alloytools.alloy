/*
 * EvaluatorTest.java
 * Created on Jun 21, 2005
 */
package tests.basic;

import java.net.URL;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import junit.framework.TestCase;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Evaluator;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Tests kodkod.engine.Evaluator using the instance produced by running the
 * AlloyAnalyzer on examples/puzzles/handshake.als
 *
 * @author Emina Torlak
 */
public class EvaluatorTest extends TestCase {

    private final String SOLUTION  = "handshake.xml";
    private final String PATH      = "examples/puzzles/handshake/";
    private final String UNIV_PATH = "alloy/lang/univ/";

    private Evaluator    evaluator;
    private Relation     univ, hilary, jocelyn, person, spouse, shaken;

    /**
     * Constructor for EvaluatorTest.
     *
     * @param arg0
     */
    public EvaluatorTest(String arg0) {
        super(arg0);
    }

    private static Relation relation(Map<String,Relation> nameToRelation, String path, String name) {
        return nameToRelation.get(path + name);
    }

    /*
     * @see TestCase#setUp()
     */
    @Override
    protected void setUp() throws Exception {
        super.setUp();

        URL resource = getClass().getResource(SOLUTION);

        evaluator = new Evaluator(InstanceCreator.getInstance(resource.openStream()));
        Map<String,Relation> nameToRelation = new HashMap<String,Relation>();
        for (Relation r : evaluator.instance().relations()) {
            nameToRelation.put(r.name(), r);
        }
        univ = relation(nameToRelation, UNIV_PATH, "univ");
        hilary = relation(nameToRelation, PATH, "Hilary");
        jocelyn = relation(nameToRelation, PATH, "Jocelyn");
        person = relation(nameToRelation, PATH, "Person");
        spouse = relation(nameToRelation, PATH, "spouse");
        shaken = relation(nameToRelation, PATH, "shaken");
    }

    /*
     * @see TestCase#tearDown()
     */
    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    private boolean eval(Formula formula) {
        return evaluator.evaluate(formula);
    }

    private Set<Tuple> eval(Expression expression) {
        return evaluator.evaluate(expression);
    }

    private Set<Tuple> value(Relation relation) {
        return evaluator.instance().tuples(relation);
    }

    public final void testEvalUnion() {
        // Hilary + Hilary = Hilary
        assertEquals(eval(hilary.union(hilary)), value(hilary));
        // Hilary + Jocelyn + Person = Person
        assertEquals(eval(hilary.union(jocelyn).union(person)), value(person));
        // spouse + shaken = spouse + shaken
        Set<Tuple> spousePlusShaken = new HashSet<Tuple>();
        spousePlusShaken.addAll(value(spouse));
        spousePlusShaken.addAll(value(shaken));
        assertEquals(eval(spouse.union(shaken)), spousePlusShaken);
        // shaken + spouse = spouse + shaken
        assertEquals(eval(shaken.union(spouse)), spousePlusShaken);
        // spouse + Person = arity mismatch
        try {
            eval(spouse.union(person));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}

    }

    public final void testEvalDifference() {
        // Jocelyn - Jocelyn = {}
        assertTrue(eval(jocelyn.difference(jocelyn)).isEmpty());
        // Hilary - Jocelyn = Hilary
        assertEquals(value(hilary), eval(hilary.difference(jocelyn)));
        // spouse + shaken - spouse = shaken
        assertEquals(value(shaken), eval(spouse.union(shaken).difference(spouse)));
        // spouse - Person = arity mismatch
        try {
            eval(spouse.difference(person));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}

    }

    public final void testEvalJoin() {
        // Hilary.spouse = Jocelyn
        assertEquals(eval(hilary.join(spouse)), value(jocelyn));
        // arity(spouse.shaken) = 2
        assertEquals(spouse.join(shaken).arity(), 2);
        // spouse.Person = univ
        assertEquals(eval(spouse.join(person)), value(univ));
        // spouse.spouse.Hilary = Hilary
        assertEquals(eval(spouse.join(spouse).join(hilary)), value(hilary));
        // (univ - Person.shaken).shaken = {}
        assertTrue(eval(univ.difference(person.join(shaken)).join(shaken)).isEmpty());
        // Hilary.Jocelyn = arity mismatch
        try {
            eval(hilary.join(jocelyn));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}
    }

    public final void testEvalProduct() {
        // Hilary->Jocelyn = Hilary->Jocelyn
        final Set<Tuple> hilaryAndJocelyn = eval(hilary.product(jocelyn));
        final Tuple hj = hilaryAndJocelyn.iterator().next();
        assertEquals(hilaryAndJocelyn.size(), 1);
        assertEquals(hj.atom(0), value(hilary).iterator().next().atom(0));
        assertEquals(hj.atom(1), value(jocelyn).iterator().next().atom(0));

        // Person->(spouse->shaken) = (Person->spouse)->shaken
        assertEquals(eval(person.product(spouse.product(shaken))), eval(person.product(spouse).product(shaken)));
        // Person->(spouse + shaken) = Person->spouse + Person->shaken
        assertEquals(eval(person.product(spouse.union(shaken))), eval(person.product(spouse).union(person.product(shaken))));
        // arity(spouse->shaken) = 4
        assertEquals(spouse.product(shaken).arity(), 4);
    }

    public final void testEvalIntersection() {
        // Hilary & Person = Hilary
        assertEquals(eval(hilary.intersection(person)), value(hilary));
        // Hilary & Person = Person & Hilary
        assertEquals(eval(hilary.intersection(person)), eval(person.intersection(hilary)));
        // spouse & shaken = {}
        assertTrue(eval(spouse.intersection(shaken)).isEmpty());
        // spouse & Person = arity mismatch
        try {
            eval(spouse.intersection(person));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}

    }

    public final void testEvalOverride() {
        // Hilary ++ Hilary = Hilary
        assertEquals(eval(hilary.override(hilary)), value(hilary));
        // Hilary ++ Jocelyn = Hilary + Jocelyn
        assertEquals(eval(hilary.override(jocelyn)), eval(hilary.union(jocelyn)));
        // spouse ++ shaken = shaken + (spouse - (shaken.Person)->Person)
        assertEquals(eval(spouse.override(shaken)), eval(shaken.union(spouse.difference(shaken.join(person).product(person)))));
    }

    public final void testEvalTranspose() {
        // ~spouse = spouse
        assertEquals(eval(spouse.transpose()), value(spouse));
        // ~(Hilary->Jocelyn) = Jocelyn->Hilary
        assertEquals(eval(hilary.product(jocelyn).transpose()), eval(jocelyn.product(hilary)));
        // ~(~shaken) = shaken
        assertEquals(eval(shaken.transpose().transpose()), value(shaken));
        // ~Person = arity error
        try {
            eval(person.transpose());
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}

    }

    public final void testEvalTransitiveClosure() {
        // // ^(Hilary->Jocelyn) = Hilary->Jocelyn
        // assertEquals(eval(hilary.product(jocelyn).closure()),
        // eval(hilary.product(jocelyn)));
        // // ^spouse = spouse + spouse.spouse
        // assertEquals(eval(spouse.closure()),
        // eval(spouse.union(spouse.join(spouse))));
        // // Hilary.^shaken = univ - (univ - Person.shaken)
        // assertEquals(eval(hilary.join(shaken.closure())),
        // eval(univ.difference(univ.difference(person.join(shaken)))));
        // try {
        // eval(person.closure());
        // fail("Expected IllegalArgumentException");
        // } catch (IllegalArgumentException iae) {}

        // ^r = value(^r)
        final Relation r = Relation.binary("r");
        final Universe u = evaluator.instance().universe();
        final TupleFactory f = u.factory();
        final Instance instance = new Instance(u);

        // value(r) = u[0]->u[1] + u[1]->u[2] + u[2]->u[3] + u[3]->u[4]
        TupleSet s = f.noneOf(r.arity());
        for (int i = 0; i < 4; i++)
            s.add(f.tuple(u.atom(i), u.atom(i + 1)));
        instance.add(r, s);
        // value(^r) = value(r) + u[0]->u[2] + u[0]->u[3] + u[0]->u[4] +
        // u[1]->u[3] u[1]->u[4] + u[2]->u[4]
        Set<Tuple> result = new HashSet<Tuple>();
        for (int i = 0; i < 4; i++) {
            for (int j = i + 1; j < 5; j++) {
                result.add(f.tuple(u.atom(i), u.atom(j)));
            }
        }
        assertEquals((new Evaluator(instance)).evaluate(r.closure()), result);
        // value(*r) = value(^r) + iden
        for (int i = 0; i < 10; i++) {
            result.add(f.tuple(u.atom(i), u.atom(i)));
        }

        assertEquals((new Evaluator(instance)).evaluate(r.reflexiveClosure()), result);
    }

    public final void testEvalSubset() {
        // Hilary in Person = true
        assertTrue(eval(hilary.in(person)));
        // shaken in spouse = false
        assertFalse(eval(shaken.in(spouse)));
        // spouse in Person->Person = true
        assertTrue(eval(spouse.in(person.product(person))));
        // spouse in Person = arity mismatch
        try {
            eval(spouse.in(person));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}
    }

    public final void testEvalEquals() {
        // Person = univ = true
        assertTrue(eval(person.eq(univ)));
        // univ = Person = true
        assertTrue(eval(univ.eq(person)));
        // spouse = shaken = false
        assertFalse(eval(spouse.eq(shaken)));
        // shaken = Person
        try {
            eval(shaken.in(person));
            fail("Expected IllegalArgumentException");
        } catch (IllegalArgumentException iae) {}
    }

    public final void testEvalAnd() {
        // Hilary in Person && Jocelyn in Person = true
        assertTrue(eval(hilary.in(person).and(jocelyn.in(person))));
        // Jocelyn in Person && Hilary in Person = true
        assertTrue(eval(jocelyn.in(person).and(hilary.in(person))));
        // shaken in spouse && univ = Person = false
        assertFalse(eval(shaken.in(spouse).and(univ.eq(person))));
        // Person = univ && spouse in shaken = false
        assertFalse(eval(person.eq(univ).and(spouse.in(shaken))));
        // spouse in shaken && Hilary = Jocelyn = false
        assertFalse(eval(spouse.in(shaken).and(hilary.eq(jocelyn))));
    }

    public final void testEvalOr() {
        // Hilary in Person || Jocelyn in Person = true
        assertTrue(eval(hilary.in(person).or(jocelyn.in(person))));
        // Jocelyn in Person || Hilary in Person = true
        assertTrue(eval(jocelyn.in(person).or(hilary.in(person))));
        // shaken in spouse || univ = Person = true
        assertTrue(eval(shaken.in(spouse).or(univ.eq(person))));
        // Person = univ || spouse in shaken = true
        assertTrue(eval(person.eq(univ).or(spouse.in(shaken))));
        // spouse in shaken || Hilary = Jocelyn = false
        assertFalse(eval(spouse.in(shaken).or(hilary.eq(jocelyn))));
    }

    public final void testEvalNot() {
        // !(Hilary in Person) = false
        assertFalse(eval(hilary.in(person).not()));
        // !(Hilary = Jocelyn) = true
        assertTrue(eval(hilary.eq(jocelyn).not()));
    }

    public final void testEvalImplies() {
        // Hilary in Person => Jocelyn in Person = true
        assertTrue(eval(hilary.in(person).implies(jocelyn.in(person))));
        // Hilary in Person => Person in Jocelyn = false
        assertFalse(eval(hilary.in(person).implies(person.in(jocelyn))));
        // Hilary = Jocelyn => Person = univ = true
        assertTrue(eval(hilary.eq(jocelyn).implies(person.eq(univ))));
        // Hilary = Jocelyn => spouse = shaken = true
        assertTrue(eval(hilary.eq(jocelyn).implies(spouse.eq(shaken))));
    }

    public final void testEvalIff() {
        // Hilary in Person <=> Jocelyn in Person = true
        assertTrue(eval(hilary.in(person).iff(jocelyn.in(person))));
        // Hilary = Jocelyn <=> spouse = shaken = true
        assertTrue(eval(hilary.eq(jocelyn).iff(spouse.eq(shaken))));
        // shaken in spouse <=> univ = Person = false
        assertFalse(eval(shaken.in(spouse).iff(univ.eq(person))));
        // Person = univ <=> spouse in shaken = false
        assertFalse(eval(person.eq(univ).iff(spouse.in(shaken))));
    }

    public final void testMultiplicityFormula() {
        // some Person = true
        assertTrue(eval(person.some()));
        // some (Person - univ) = false
        assertFalse(eval(person.difference(univ).some()));
        // no Person = false
        assertFalse(eval(person.no()));
        // no (Person - univ) = true
        assertTrue(eval(person.difference(univ).no()));
        // one Hilary = true
        assertTrue(eval(hilary.one()));
        // one spouse = false
        assertFalse(eval(spouse.one()));
        // lone (Person - univ) = true
        assertTrue(eval(person.difference(univ).lone()));
        // lone shaken = false
        assertFalse(eval(shaken.lone()));

    }

    public final void testQuantifiedFormula() {

        final Variable p = Variable.unary("p"), q = Variable.unary("q");
        final Decl pdecl = p.oneOf(person), qdecl = q.oneOf(person);
        final Decls pqdecls = pdecl.and(qdecl);
        // all p: Person | some p.spouse = true
        assertTrue(eval(p.join(spouse).some().forAll(pdecl)));
        // all p, q: Person | (p.spouse = q) => ! (q in p.shaken) = true
        assertTrue(eval((p.join(spouse).eq(q).implies(q.in(p.join(shaken)).not()).forAll(pqdecls))));
        // some p: Person | no p.shaken = true
        assertTrue(eval(p.join(shaken).no().forSome(pdecl)));
        // all p: Person | some q: Person | p.shaken = q = false
        assertFalse(eval((p.join(shaken).eq(q).forSome(qdecl)).forAll(pdecl)));
        // some p, q: Person | !(p = q) && (p.shaken = q.shaken) = true
        assertTrue(eval(p.eq(q).not().and(p.join(shaken).eq(q.join(shaken))).forSome(pqdecls)));
        // some p: Person | all q: Person-p | p in q.shaken = false
        assertFalse(eval((p.in(q.join(shaken)).forAll(q.oneOf(person.difference(p)))).forSome(pdecl)));
    }

    public final void testComprehension() {
        final Variable[] vars = new Variable[3];
        final Decl[] decls = new Decl[3];
        for (int i = 0; i < 3; i++) {
            Variable v = Variable.unary("v" + i);
            Decl d = v.oneOf(person);
            vars[i] = v;
            decls[i] = d;
        }

        // {v0: Person | no v0.shaken} = univ - shaken.Person
        assertEquals(eval(vars[0].join(shaken).no().comprehension(decls[0])), eval(univ.difference(shaken.join(person))));
        // {v0, v1: Person | v1 in v0.shaken} = shaken
        assertEquals(eval(vars[1].in(vars[0].join(shaken)).comprehension(decls[0].and(decls[1]))), value(shaken));
        // {v0, v1, v2: Person | no v1.shaken} = Person->(univ -
        // shaken.Person)->Person
        assertEquals(eval(vars[1].join(shaken).no().comprehension(decls[0].and(decls[1]).and(decls[2]))), eval(person.product(univ.difference(shaken.join(person))).product(person)));
    }

}
