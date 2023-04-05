/*
	Tests for appropriate parsing failures.

	It tests every file in src/resources/parsefail
	to make sure it fails parsing.
*/

package org.alloytools.alloy.dash;

import java.util.*;
import java.io.IOException;
import java.io.File;
import java.nio.file.Files;
import java.nio.charset.Charset;
import java.util.stream.Stream;
import java.util.stream.IntStream;
import java.util.Collections;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import org.apache.commons.io.FileUtils;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;

import java.net.URL;  


import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorFatal;

import ca.uwaterloo.watform.core.DashErrors;
import ca.uwaterloo.watform.core.DashOptions;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;




@RunWith(Parameterized.class)

public class DashParseFailTests {

	private static String resourcePath = "src/test/resources/parsefail";
   	private final String fileName;

   	public DashParseFailTests(String f) {
   	   this.fileName = f;
   	}

   // list of file names that are parameters to test 
   @Parameterized.Parameters
   public static List<String> fileNames() {
   		File dir = new File(resourcePath);
  		return Arrays.asList(dir.listFiles()).stream().filter(i -> !i.isHidden()).map (i -> i.getName()).collect(Collectors.toList());

   }

   @Test
	public void test() {
		File dir = new File(resourcePath);
		String absolutePath = new File(resourcePath).getAbsolutePath();
    	assertThrows(ErrorSyntax.class, () -> {
    		DashUtil.parseEverything_fromFileDash(null,null,absolutePath+"/"+fileName);
    	});
	}




	// leftover - not used because multiline strings in Java 1.8 are a pain
    @Rule
    public TemporaryFolder folder= new TemporaryFolder();

    // leftover - not used because multiline strings in Java 1.8 are a pain
    // uses	static DashModule parseEverything_fromStringDash(A4Reporter rep, String content)
    public DashModule parseFromString(String content) throws IOException {
        File tmpFile = folder.newFile("myfile.txt");
        FileUtils.writeStringToFile(tmpFile, content, Charset.defaultCharset());
        return DashUtil.parseEverything_fromFileDash(null, null, tmpFile.getCanonicalPath());
    	//Note: File is guaranteed to be deleted after the test finishes.
	}

	/*
  	// src/test/resource is not getting copied to the classpath
  	// so we'll use an alternative
  	@Test 
  	public void parseTest1() {
  		File dir = new File(resourcePath);
  		int fileCount = countFilesInCurrentDirectory(dir);
  		assertTrue(fileCount == 1);
		// String absolutePath = new File(resourcePath).getAbsolutePath();
  		//DashUtil.parseEverything_fromFileDash(null,null,absolutePath+"/test1.dsh");
  	}
  	*/


 }
