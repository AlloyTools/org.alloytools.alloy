package org.alloytools.alloy.java.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.TField;
import org.alloytools.alloy.core.api.TSig;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.IAtom;
import org.alloytools.alloy.solver.api.ITuple;
import org.alloytools.alloy.solver.api.ITupleSet;

public class AlloyJava {

	public interface Instance {
		Object get(IAtom atom);

		Object get(ITupleSet tuples);

		<T> List<T> get(Class<T> class1) throws Exception;
	}

	final Map<TSig, Function<Object, ?>>	converters	= new HashMap<>();
	final AlloyModule						module;

	public AlloyJava(AlloyModule module) {
		this.module = module;
	}

	public <T> AlloyJava addConverter(Class<T> clazz, TSig sig, Function<Object, T> converter) {
		converters.put(sig, converter);
		return this;
	}

	public Instance instance(AlloyInstance instance) {
		Map<IAtom, Object> values = new IdentityHashMap<>();

		return new Instance() {

			@Override
			public Object get(IAtom atom) {
				return values.computeIfAbsent(atom, a -> {
					TSig sig = atom.getSig();
					Map<String, Object> map = new HashMap<>();
					List<? extends TField> fields = sig.getFields();
					for (TField field : fields) {

						ITupleSet tuples = instance.getField(field);
						ITupleSet values = atom.join(tuples);
						map.put(field.getName(), get(values));
					}
					Object from;
					if (map.isEmpty())
						from = atom.getValue();
					else
						from = map;

					Function<Object, ?> function = converters.get(sig);
					if (function != null) {
						return function.apply(from);
					} else {
						return from;
					}
				});
			}

			@Override
			public Object get(ITupleSet values) {

				if (values.size() == 0)
					return null;

				if (values.isScalar()) {
					IAtom value = values.scalar();
					return get(value);
				}

				if (values.isList()) {
					List<Object> list = new ArrayList<>();
					for (ITuple tuple : values) {

						IAtom entry = tuple.get(0);
						list.add(get(entry));

					}
					return list;
				}

				List<IAtom> left = values.asList();
				Map<Object, Object> map = new HashMap<>();
				for (IAtom key : left) {
					ITupleSet right = key.join(values);
					map.put(get(key), get(right));
				}
				return map;
			}

			@Override
			public <T> List<T> get(Class<T> class1) throws Exception {
				TSig sig = module.getSig( class1.getSimpleName()).orElse(null);
				ITupleSet atoms = instance.getAtoms(sig);
				
				List<T> result = new ArrayList<>();
				for ( ITuple tuple : atoms) {
					Object v = get(tuple.get(0));
					T cnv = null;// TODO Converter.cnv(class1, v);
					result.add(cnv);
				}
				return result;
			}
		};
	}

}
