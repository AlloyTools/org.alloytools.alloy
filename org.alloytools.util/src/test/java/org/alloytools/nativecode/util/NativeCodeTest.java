package org.alloytools.nativecode.util;

import static org.junit.Assert.assertNotNull;

import org.alloytools.nativecode.util.NativeCode.Platform;
import org.junit.Test;

public class NativeCodeTest {

	@Test
	public void testNative() {
		Platform platform = NativeCode.platform;
		assertNotNull(platform);
		System.out.println(platform);
	}
}
