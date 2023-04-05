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
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;

import edu.mit.csail.sdg.alloy4.A4Reporter;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;

public class DashStateTests {

	private static String resourcePath = "src/test/resources/pass";
 
    public static DashModule test(String fileName) {
      File dir = new File(resourcePath);
      String absolutePath = new File(resourcePath).getAbsolutePath();
      A4Reporter rep = new A4Reporter();
      return MainFunctions.parseAndResolveDashFile(absolutePath+"/"+fileName+".dsh", rep);
   }
   public List<String> ll(String[] k) {
      return Arrays.asList(k);
   }

   // src/dest ------------------

   public static String src(DashModule d, String s) {
      return d.getTransSrc(s).toString();
   }
   public static String dest(DashModule d, String s) {
      return d.getTransDest(s).toString();
   }

   @Test 
   public void noDefaultNeededTest1() {
      DashModule d = test("noDefaultNeeded1");
      List<String> result = Arrays.asList(new String[]{"Root/S"});
      assertTrue(d.getDefaults("Root").equals(result));
   }
   @Test 
   public void noDefaultNeededTest2() {
      DashModule d = test("noDefaultNeeded2");
      List<String> result = Arrays.asList(new String[]{"Root/C"});
      assertTrue(d.getDefaults("Root").equals(result));
   }
   
   @Test 
   public void noSrcDest1() {
      DashModule d = test("noSrcDest1");
      assertTrue(src(d,"Root/t1").equals("Root[]"));
      assertTrue(dest(d,"Root/t1").equals("Root[]"));
   }
   @Test 
   public void noSrc1() {
      DashModule d = test("noSrc1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1[]"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2[]")); 
   }
   @Test 
   public void noSrc2() {
      DashModule d = test("noSrc2");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1[]"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2/S3/S4[]"));
   }

   @Test 
   public void otherSrcDest1() {
      DashModule d = test("otherSrcDest1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1[]"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2/S3/S4[]"));
      assertTrue(src(d,"Root/S2/t2").equals("Root/S2/S3[]"));
      assertTrue(dest(d,"Root/S2/t2").equals("Root/S2[]"));
   }

   @Test 
   public void srcDestFQN1() {
      DashModule d = test("srcDestFQN1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1[]"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S1/S7[]"));
      assertTrue(src(d,"Root/S2/S3/S4/t2").equals("Root/S2/S3/S4[]"));
      assertTrue(dest(d,"Root/S2/S3/S4/t2").equals("Root/S1/S7[]"));
   }
  
   @Test 
   public void paramSrcDest1() {
      DashModule d = test("paramSrcDest1");
      assertTrue(src(d,"Root/A/t1").equals("Root/A[pAPID]"));
      assertTrue(dest(d,"Root/A/t1").equals("Root/A[pAPID]"));      
   }   
   @Test 
   public void paramSrcDest2() {
      DashModule d = test("paramSrcDest2");
      assertTrue(src(d,"Root/A/t1").equals("Root/A[pAPID]"));
      assertTrue(dest(d,"Root/A/t1").equals("Root/B/S1[x]"));      
   }  

   // getAllAnces --------------

   @Test 
   public void getAllAnces1() {
      DashModule d = test("noSrc1");
      assertTrue(d.getAllAnces("Root/S1").equals(ll(new String[]{"Root", "Root/S1"})));
   }

   // getClosestConcAnces ----------------

   @Test 
   public void getClosestConcAnces1() {
      DashModule d = test("noSrc1");
      assertTrue(d.getClosestConcAnces("Root/S1").equals("Root"));
      assertTrue(d.getClosestConcAnces("Root/S2").equals("Root"));
   }
   @Test 
   public void getClosestConcAnces2() {
      DashModule d = test("scopeParam2");
      assertTrue(d.getClosestConcAnces("Root/A/B/S1").equals("Root/A/B"));
      assertTrue(d.getClosestConcAnces("Root/A/B").equals("Root/A/B"));
   }

   // getAllNonConcDesc --------------

   @Test 
   public void getAllNonConcDesc1() {
      DashModule d = test("getAllNonConcDesc1");
      assertTrue(d.getAllNonConcDesc("Root")
         .equals(ll(new String[]{"Root", "Root/S1", "Root/S1/S2","Root/S3","Root/S3/S4", "Root/S3/S4/S5"})));
   }

   // getRegion ----------------------
   @Test 
   public void getRegion1() {
      DashModule d = test("getRegion1");
      assertTrue(d.getRegion("Root/S1/S2")
         .equals(ll(new String[]{"Root", "Root/S1", "Root/S1/S2","Root/S3","Root/S3/S4", "Root/S3/S4/S5"})));
   }
   @Test 
   public void getRegion2() {
      DashModule d = test("getAllNonConcDesc1");
      assertTrue(d.getRegion("Root/S1/S2")
         .equals(ll(new String[]{"Root", "Root/S1", "Root/S1/S2","Root/S3","Root/S3/S4", "Root/S3/S4/S5"})));
   }

   // getLeafStatesExited --------------------

   public List<String> exited(DashModule d, String tfqn) {
      return d.getLeafStatesExited(d.getTransSrc(tfqn))
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   } 

   @Test 
   public void getLeafStatesExited1() {
      DashModule d = test("noSrc1");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1[]"
         })));
   }
   @Test 
   public void getLeafStatesExited2() {
      DashModule d = test("noSrc2");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1[]"
         })));
   }
   @Test 
   public void getLeafStatesExited3() {
      DashModule d = test("noDefaultNeeded2");
      assertTrue(
         exited(d,"Root/C/t1")
         .equals(ll(new String[]{
            "Root/C[]"
         })));
   }
   @Test 
   public void getLeafStatesExited4() {
      DashModule d = test("noSrcDest1");
      assertTrue(
         exited(d,"Root/t1")
         .equals(ll(new String[]{
            "Root[]"
         })));
   }
   @Test 
   public void getLeafStatesExited5() {
      DashModule d = test("otherSrcDest1");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1[]"
         })));
      assertTrue(
         exited(d,"Root/S2/t2")
         .equals(ll(new String[]{
            "Root/S2/S3/S4[]"
         })));
   }
   @Test 
   public void getLeafStatesExited6() {
      DashModule d = test("paramSrcDest1");
      assertTrue(
         exited(d,"Root/A/t1")
         .equals(ll(new String[]{
            "Root/A[pAPID]"
         })));
   }
   @Test 
   public void getLeafStatesExited7() {
      DashModule d = test("paramSrcDest3");
      assertTrue(
         exited(d,"Root/A/t1")
         .equals(ll(new String[]{
            "Root/B/S1[x]"
         })));
   }

   // getScope -------------------------------
   @Test 
   public void getScope1() {
      DashModule d = test("scopeParam1");
      assertTrue(
         d.getScope("Root/A/S1/t1").toString()
         .equals("Root/A[(pAPID = x => pAPID else APID)]"));
   }
   @Test 
   public void getScope2() {
      DashModule d = test("scopeParam2");
      assertTrue(
         d.getScope("Root/A/B/S1/t1").toString()
         .equals("Root/A/B[(pAPID = x => pAPID else APID), (AND[pAPID = x, pBPID = y] => pBPID else BPID)]"));
   }
   @Test 
   public void getScope3() {
      DashModule d = test("scopeParam3");
      assertTrue(
         d.getScope("Root/A/B/S1/t1").toString()
         .equals("Root/A/B[pAPID, pBPID]"));
   }

   // getLeafStatesEntered -----------------
   public List<String> entered(DashModule d, String tfqn) {
      return d.getLeafStatesEntered(d.getTransDest(tfqn))
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   } 

   @Test 
   public void getLeafStatesEntered1() {
      DashModule d = test("noSrc1");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2[]"
         })));
   }
   @Test 
   public void getLeafStatesEntered2() {
      DashModule d = test("noSrc2");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/S3/S4[]"
         })));
   }
}
