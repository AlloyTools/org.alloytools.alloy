/*
   let's check that the tests in the pass directory
   pass the parse and wff checks first 
*/

package org.alloytools.alloy.dash;

import java.util.*;
import java.io.File;
import java.util.Collections;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import ca.uwaterloo.watform.parser.DashUtil;




@RunWith(Parameterized.class)

public class DashPassParseWffTests {

	private static String resourcePath = "src/test/resources/pass";
   	private final String fileName;

   	public DashPassParseWffTests(String f) {
   	   this.fileName = f;
   	}

   // list of file names that are parameters to test 
   @Parameterized.Parameters
   public static List<String> fileNames() {
   		File dir = new File(resourcePath);
  		//int fileCount = countFilesInCurrentDirectory(dir);
  		// filenaming starts at 0
  		return Arrays.asList(dir.listFiles())
         .stream()
         .filter(i -> !i.isHidden())
         .map (i -> i.getName())
         .collect(Collectors.toList());

   }

   @Test
	public void test() {
		File dir = new File(resourcePath);
		String absolutePath = new File(resourcePath).getAbsolutePath();
     	DashUtil.parseEverything_fromFileDash(null,null,absolutePath+"/"+fileName);
	}


 }
