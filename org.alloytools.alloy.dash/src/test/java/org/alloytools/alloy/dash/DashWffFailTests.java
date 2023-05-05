/*
   The purpose of these tests is to check that wff errors (DashErrors) are caught.
   All files tested here should pass parsing and raise DashErrors during resolveAllDash
   All of these raise exceptions.
*/


// junit 4 does not seem to have a way to assert that
// an exception is not thrown
// junit 5 has assertAll()

package org.alloytools.alloy.dash;

import java.util.*;
import java.io.File;
import java.util.Collections;
import java.util.stream.Collectors;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.A4Reporter;

import static ca.uwaterloo.watform.core.DashErrors.*;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;

@RunWith(Parameterized.class)

public class DashWffFailTests {

   private static String resourcePath = "src/test/resources/wfffail";

   public static void test(String fileName) {
      File dir = new File(resourcePath);
      String absolutePath = new File(resourcePath).getAbsolutePath();
      A4Reporter rep = new A4Reporter();
      DashModule d = MainFunctions.parseAndResolveDashFile(absolutePath+"/"+fileName, rep);
   }

	private final String fileName;
   private final String msg;

	public DashWffFailTests(String f, String msg) {
	   this.fileName = f;
      this.msg = msg;
	}

   // list of file names that are parameters to test 
   @Parameterized.Parameters
   public static Collection fileNameMsg() {
      return Arrays.asList(new Object[][] {
         {"noStates1", noStatesMsg},
         {"noStates2", noStatesMsg},
         {"onlyOneState1", onlyOneStateMsg},
         {"onlyOneState2", onlyOneStateMsg},
         {"noTrans1", noTransMsg}, // 4
         {"noTrans2", noTransMsg},
         {"noDefaultState1", noDefaultStateMsg},
         {"noDefaultState2", noDefaultStateMsg},
         {"tooManyDefaultStates1", tooManyDefaultStatesMsg},
         {"tooManyDefaultStates2", tooManyDefaultStatesMsg},
         {"allConcDefaultStates1",allConcDefaultStatesMsg},
         {"allConcDefaultStates2",allConcDefaultStatesMsg},
         {"stateNameCantBeFQN1", stateNameCantBeFQNMsg},
         {"stateNameCantBeFQN2", stateNameCantBeFQNMsg},
         {"dupSiblingNames1", dupSiblingNamesMsg},
         {"dupSiblingNames2", dupSiblingNamesMsg},
         {"dupTransName1", dupTransNameMsg},
         {"dupTransName2", dupTransNameMsg}, // 17
         {"moreThanOneSrcDest1", tooManyMsg},
         {"moreThanOneSrcDest2", tooManyMsg}, // 19
         {"moreThanOneSrcDest3", tooManyMsg},
         //{"unknownSrcDest1", unknownSrcDestMsg}, //21
         //{"unknownSrcDest2", unknownSrcDestMsg},
         //{"unknownSrcDest3", unknownSrcDestMsg},
         {"unknownSrcDest4", unknownSrcDestMsg},
         {"fqnSrcDestMustHaveRightNumberParams1", fqnSrcDestMustHaveRightNumberParamsMsg}, 
         {"srcDestCantHaveParam1", srcDestCantHaveParamMsg},
         {"ambiguousSrcDest1", ambiguousSrcDestMsg},
         {"test11",ambiguousSrcDestMsg}
      });
   }

   @Test
	public void test() {
      Exception exception = assertThrows(ErrorSyntax.class, () -> {
         test(fileName + ".dsh");
      });
      String actualMessage = exception.getMessage();
      assertTrue(actualMessage.contains(msg)); 
	}

 }
