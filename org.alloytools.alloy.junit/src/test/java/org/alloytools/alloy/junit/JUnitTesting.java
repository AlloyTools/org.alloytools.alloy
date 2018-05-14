package org.alloytools.alloy.junit;

import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.alloytools.alloy.junit.util.AlloyJUnit;
import org.junit.Test;

import aQute.lib.io.IO;

public class JUnitTesting {

	@Test
	public void testSimple() throws Exception {
		File file = IO.getFile("src/test/resources/testprgs/collection.als");
		AlloyJUnit x = new AlloyJUnit(file);
	}
}
