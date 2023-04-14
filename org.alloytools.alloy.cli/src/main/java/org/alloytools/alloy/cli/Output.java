package org.alloytools.alloy.cli;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import aQute.lib.json.JSONCodec;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;

public class Output {

	public static class InstanceDTO {
		public int						state=-1;
		public boolean					loopstate;
		public List<String>				atoms		= new ArrayList<>();
		public Map<String, String[][]>	relations	= new TreeMap<>();
		public Map<String, Object>		skolems		= new TreeMap<>();
	}

	public static class FieldDTO {
		public String	name;
		public boolean	ambiguous;
		public boolean	defined;
		public boolean	isMeta;
		public boolean	isPrivate;
		public boolean	isVariable;
		public long		weight;
		public String	explain;
		public String	type;

	}

	public static class SigDefDTO {
		public String			name;
		public String			explain;
		public boolean			isAbstract;
		public boolean			isSubsig;
		public boolean			isSubset;
		public boolean			isLone;
		public boolean			isOne;
		public boolean			isSome;
		public boolean			isPrivate;
		public boolean			isEnum;
		public boolean			isMeta;
		public boolean			builtin;
		public String			type;
		public List<FieldDTO>	fields	= new ArrayList<>();
	}

	public static class SolutionDTO {
		public List<InstanceDTO>	instances	= new ArrayList<>();
		public long					utctime;
		public String				localtime;
		public int					bitwidth;
		public int					unrolls;
		public String				command;
		public int					max;
		public int					min;
		public boolean				satisfiable;
		public boolean				incremental;
		public String				fileName;

		public List<SigDefDTO>		sigs		= new ArrayList<>();
		public String				moduleName;
	}

	private static SigDefDTO toDTO(Sig sig) {
		SigDefDTO sigdto = new SigDefDTO();
		sigdto.name = sig.label;
		sigdto.explain = sig.explain();
		sigdto.builtin = sig.builtin;
		sigdto.isAbstract = sig.isAbstract != null;
		sigdto.isSubsig = sig.isSubsig != null;
		sigdto.isSubset = sig.isSubset != null;
		sigdto.isLone = sig.isLone != null;
		sigdto.isOne = sig.isOne != null;
		sigdto.isSome = sig.isSome != null;
		sigdto.isPrivate = sig.isPrivate != null;
		sigdto.isEnum = sig.isEnum != null;
		sigdto.isMeta = sig.isMeta != null;
		sigdto.type = sig.type().toString();

		for (Field field : sig.getFields()) {
			sigdto.fields.add(toDTO(field));
		}
		return sigdto;
	}

	private static FieldDTO toDTO(Field field) {
		FieldDTO flddto = new FieldDTO();
		flddto.name = field.label;
		flddto.ambiguous = field.ambiguous;
		flddto.defined = field.defined;
		flddto.isMeta = field.isMeta != null;
		flddto.isPrivate = field.isPrivate != null;
		flddto.isVariable = field.isVariable != null;
		flddto.weight = field.weight;
		flddto.explain = field.explain();
		flddto.type = field.type().toString();

		return flddto;
	}

	/**
	 * Turn a solution into a JSON string
	 * 
	 * @param world
	 *            the module that was compiled
	 * @param s
	 * @return
	 * @throws Exception
	 */

	public static String json(Module world, A4Solution s) throws Exception {
		SolutionDTO sol = new SolutionDTO();
		sol.utctime = System.currentTimeMillis();
		sol.localtime = LocalDateTime.now(ZoneId.systemDefault()).toString();
		sol.bitwidth = s.getBitwidth();
		sol.command = s.getOriginalCommand();
		sol.moduleName = world.getModelName();
		sol.fileName = world.path() == null ? s.getOriginalFilename() : world.path();
		sol.incremental = s.isIncremental();
		sol.max = s.max();
		sol.min = s.min();
		sol.satisfiable = s.satisfiable();
		sol.unrolls = s.unrolls();

		Set<Field> fields = new LinkedHashSet<>();

		for (Sig sig : world.getAllReachableSigs()) {
			if (sig.isPrivate != null)
				continue;

			sol.sigs.add(toDTO(sig));

			for (Field field : sig.getFields()) {
				if (field.isPrivate != null)
					continue;
				fields.add(field);
			}
		}

		if (s.satisfiable()) {

			for (int state = 0; state < s.getTraceLength(); state++) {
				int loopstate = s.getLoopState();

				System.out.println("trace " + state);
				InstanceDTO instance = new InstanceDTO();
				instance.state = state;
				instance.loopstate = state == loopstate;

				for (ExprVar atom : s.getAllAtoms()) {
					instance.atoms.add(atom.label);
				}

				for (Field field : fields) {
					if (field.isPrivate != null)
						continue;

					A4TupleSet eval = s.eval(field, state);
					if (eval.arity() == 1 || eval.size() == 0)
						continue;

					String[][] relation = new String[eval.size()][];
					int row = 0;
					for (A4Tuple t : eval) {
						assert t.arity() == eval.arity();

						String[] tuple = new String[eval.arity()];

						for (int col = 0; col < eval.arity(); col++) {
							String atom = t.atom(col);
							tuple[col] = atom;
						}
						relation[row++] = tuple;
					}

					for (ExprVar e : s.getAllSkolems()) {
						instance.skolems.put(field.label, s.eval(e, state));
					}
					instance.relations.put(field.label, relation);
				}

				sol.instances.add(instance);

				if (s.isIncremental()) {
					s = s.next();
				} else
					break;

			}
		}

		JSONCodec codec = new JSONCodec();
		return codec.enc().indent("  ").put(sol).toString();
	}

	public static String boxes(Module world, A4Solution s) {
		StringWriter sw = new StringWriter();
		try (PrintWriter pw = new PrintWriter(sw)) {
			if (!s.satisfiable()) {
				return null;
			}
			for (int i = 0; i < s.getTraceLength(); i++) {
				String format = s.format(i);
				if (i == s.getLoopState())
					pw.println(">>> loop state >-" + i + "------------------");
				else
					pw.println("-----------------" + i + "------------------");

				pw.println(format);

				if (s.isIncremental()) {
					s = s.next();
				} else
					break;
			}
			return sw.toString();
		}
	}

	public static String xml(Module world, A4Solution s) {
		StringWriter sw = new StringWriter();
		try (PrintWriter pw = new PrintWriter(sw)) {
			A4SolutionWriter.writeInstance(null, s, pw, Collections.emptyList(), Collections.emptyMap());
			return sw.toString();
		}
	}

}
