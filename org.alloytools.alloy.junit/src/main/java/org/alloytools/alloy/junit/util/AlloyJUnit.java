package org.alloytools.alloy.junit.util;

import java.io.File;
import java.lang.reflect.Method;
import java.util.List;

import org.alloytools.alloy.core.api.AlloyModule;
import org.alloytools.alloy.core.api.Command;
import org.alloytools.alloy.java.util.AlloyJava;
import org.alloytools.alloy.provider.AlloyImpl;
import org.alloytools.alloy.solver.api.AlloyInstance;
import org.alloytools.alloy.solver.api.AlloySolution;

import aQute.lib.converter.Converter;

public class AlloyJUnit {

	static class Trace {
		public Object	receiver;
		public String	op;
		public Object[]	args;
		public Object	result;
	}

	private AlloyModule	module;
	private AlloyImpl	alloy;
	private AlloyJava java;

	public AlloyJUnit(File file) throws Exception {
		alloy = new AlloyImpl();
		module = alloy.compiler().compile(file);
		java = new AlloyJava(module);
	}

	public <T> void test(String run, T implementation) throws Exception {
		List<Command> commands = module.getCommands();
		for (Command command : commands) {
			AlloySolution solution = alloy.getDefaultSolver().run(module, command);
			for ( AlloyInstance instance : solution) {
				AlloyJava.Instance js = java.instance(instance);
				List<Trace> traces = js.get(Trace.class);
				for (int i = 1; i < traces.size(); i++) {
					Trace trace = traces.get(i);
					System.out.println("Trace "+trace);
				}
			}
		}
	}

	public Object call(AlloySolution solution, Object implementation, String op, Object[] args) throws Exception {
		Class<?> clazz = implementation.getClass();
		Method[] methods = clazz.getMethods();
		for (Method m : methods) {
			m.setAccessible(true);
			if (m.getName().matches(op)) {
				if (m.getParameterCount() == args.length) {

					Object argstyped[] = new Object[args.length];
					for (int i = 0; i < args.length; i++) {

						argstyped[i] = Converter.cnv(m.getGenericParameterTypes()[i], args[i]);

					}

					return m.invoke(implementation, argstyped);
				}
			}
		}
		return false;
	}

	public AlloyModule getModule() {
		// TODO Auto-generated method stub
		return null;
	}
}
