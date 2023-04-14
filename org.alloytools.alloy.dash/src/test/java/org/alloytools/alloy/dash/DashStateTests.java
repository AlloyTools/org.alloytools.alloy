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

   // allPrefixDashRefs ----------------------
   
   public List<String> allPrefixDashRefs(DashModule d, String tfqn) {
      return d.allPrefixDashRefs(d.getScope(tfqn))
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   }    
   @Test
   public void allPrefixDashRefs1() {
      DashModule d = test("scopeParam1");
      assertTrue(
         allPrefixDashRefs(d,"Root/A/S1/t1")
         .equals(ll(new String[]{
            "Root[]",
            "Root/A[(pAPID = x => pAPID else APID)]"
         })));     
   }
   @Test
   public void allPrefixDashRefs2() {
      DashModule d = test("scopeParam2");
      assertTrue(
         allPrefixDashRefs(d, "Root/A/B/S1/t1")
         .equals(ll(new String[]{
            "Root[]",
            "Root/A[(pAPID = x => pAPID else APID)]",
            "Root/A/B[(pAPID = x => pAPID else APID), (AND[pAPID = x, pBPID = y] => pBPID else BPID)]"
         })));     
   }
   @Test
   public void allPrefixDashRefs3() {
      DashModule d = test("scopeParam3");
      assertTrue(
         allPrefixDashRefs(d, "Root/A/B/S1/t1")
         .equals(ll(new String[]{
            "Root[]",
            "Root/A[pAPID]",
            "Root/A/B[pAPID, pBPID]"
         })));     
   }
   @Test
   public void allPrefixDashRefs4() {
      DashModule d = test("getEntered5");
      assertTrue(
         allPrefixDashRefs(d, "Root/S1/t1")
         .equals(ll(new String[]{
            "Root[]",
         })));     
   }

   // getLeafStatesExited --------------------

   public List<String> exited(DashModule d, String tfqn) {
      return d.exited(tfqn)
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
            "Root/S1[]",
            "Root/S2[]"
         })));
   }
   @Test 
   public void getLeafStatesExited2() {
      DashModule d = test("noSrc2");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1[]",
            "Root/S2/S3/S4[]"
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
            "Root/S1[]",
            "Root/S2/S3/S4[]"
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
            "Root/A[APID]",
            "Root/B/S1[BPID]"
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
   @Test 
   public void getLeafStatesEntered3() {
      DashModule d = test("scopeParam1");
      assertTrue(
         entered(d,"Root/A/S1/t1")
         .equals(ll(new String[]{
            "Root/A/S2[x]"
         })));
   }
   @Test 
   public void getLeafStatesEntered4() {
      DashModule d = test("scopeParam2");
      assertTrue(
         entered(d,"Root/A/B/S1/t1")
         .equals(ll(new String[]{
            "Root/A/B/S2[x, y]"
         })));
   }
   @Test 
   public void getLeafStatesEntered5() {
      DashModule d = test("getEntered5");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A[]"
         })));
   }
   @Test 
   public void getLeafStatesEntered6() {
      DashModule d = test("getEntered6");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3[]"
         })));
   }
   @Test 
   public void getLeafStatesEntered7() {
      DashModule d = test("getEntered7");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3[AID]"
         })));
   }
   @Test 
   public void getLeafStatesEntered8() {
      DashModule d = test("getEntered8");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]", 
            "Root/S2/A/C[AID, CID]"
         })));
   }
   @Test 
   public void getLeafStatesEntered9() {
      DashModule d = test("getEntered9");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]", 
            "Root/S2/A/C/S5[AID, CID]",
         })));
   }
   @Test 
   public void getLeafStatesEntered10() {
      DashModule d = test("getEntered10");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]", 
            "Root/S2/A/C/D/S5[AID, CID, DID]",
            "Root/S2/A/C/E/S7[AID, CID, EID]"
         })));
   }
   @Test 
   public void getLeafStatesEntered11() {
      DashModule d = test("getEntered11");
      assertTrue(
         entered(d,"Root/A/S1/t1")
         .equals(ll(new String[]{
            "Root/B/S2/C/S3[x, CID]"
         })));
   }

   // getLeafStatesEnteredInContext -----------------
   
   public List<String> enteredInContext(DashModule d, String tfqn) {
      return d.entered(tfqn)
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   } 

   @Test 
   public void getLeafStatesEnteredInContext1() {
      DashModule d = test("noSrc1");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2[]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext2() {
      DashModule d = test("getEnteredInContext2");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/B/S3[]",
            "Root/A/S2[]",
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext3() {
      DashModule d = test("getEntered5");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A[]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext4() {
      DashModule d = test("getEntered6");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3[]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext5() {
      DashModule d = test("getEntered7");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3[AID]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext6() {
      DashModule d = test("getEntered8");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]",
            "Root/S2/A/C[AID, CID]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInContext7() {
      DashModule d = test("getEntered9");
      assertTrue(
         enteredInContext(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]", 
            "Root/S2/A/C/S5[AID, CID]",
         })));
   }

   // connected tests on one model
   @Test
   public void getEnteredinContext3Tests() {
      DashModule d = test("getEnteredInContext3");
      String tfqn = "Root/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/C/S2[c1]"));
      assertTrue(
         d.getScope(tfqn).toString().equals("Root[]"));
      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[AID, BID]", 
            "Root/C/S2[CID]"
         })));
      assertTrue(
         enteredInContext(d,tfqn)
         .equals(ll(new String[]{
            "Root/C/S2[CID - c1]", 
            "Root/A/B/S1[c1, AID, BID]", 
            "Root/C/S2[c1]"
         })));
      
   }
   @Test
   public void overall1() {
      DashModule d = test("overall1");
      String tfqn = "Root/A/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[pAID, pBID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/S1[a2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(pAID = a2 => pAID else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(pAID = a2 => pAID else AID), BID]", 
            "Root/A/S1[(pAID = a2 => pAID else AID)]"
         })));
      assertTrue(
         enteredInContext(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S1[AID - a2]", 
            "Root/A/S1[a2]", 
         })));      
   }
   
   @Test
   public void overall2() {
      DashModule d = test("overall2");
      String tfqn = "Root/A/S2/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/S2[pAID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(pAID = a1 => pAID else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(pAID = a1 => pAID else AID), BID]", 
            "Root/A/S2[(pAID = a1 => pAID else AID)]"
         })));
      assertTrue(
         enteredInContext(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S2[AID - a1]",  
            "Root/A/B/S1[a1, BID - b1]", 
            "Root/A/B/S1[a1, b1]"
         })));      
   }

   @Test
   public void overall3() {
      DashModule d = test("overall3");
      String tfqn = "Root/A/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/S1[a2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(a1 = a2 => a1 else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a1 = a2 => a1 else AID), BID]", 
            "Root/A/S1[(a1 = a2 => a1 else AID)]"
         })));
      assertTrue(
         enteredInContext(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[AID - a2, BID]", 
            "Root/A/S1[a2]"
         })));      
   }   
   /*
   @Test
   public void overall4() {
      DashModule d = test("overall4");
      String tfqn = "Root/A/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A[a2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(a1 = a2 => a1 else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a1 = a2 => a1 else AID), BID]", 
         })));
      assertTrue(
         enteredInContext(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[AID - a2, BID]", 
            "Root/A/B/S1[a2, BID - b1]"
            "Root/A/B/S1[a2, b1]"
         })));      
   }
   */
}
