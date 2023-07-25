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

public class DashModuleTests {

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

   // helper functions ------------------

   public static String src(DashModule d, String s) {
      return d.getTransSrc(s).toString();
   }
   public static String dest(DashModule d, String s) {
      return d.getTransDest(s).toString();
   }

   public List<String> allPrefixDashRefs(DashModule d, String tfqn) {
      return d.allPrefixDashRefs(d.getScope(tfqn))
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   }

   // src/dest ----------------
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
      assertTrue(src(d,"Root/t1").equals("Root"));
      assertTrue(dest(d,"Root/t1").equals("Root"));
   }
   @Test 
   public void noSrc1() {
      DashModule d = test("noSrc1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2")); 
   }
   @Test 
   public void noSrc2() {
      DashModule d = test("noSrc2");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2"));
   }

   @Test 
   public void otherSrcDest1() {
      DashModule d = test("otherSrcDest1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S2/S3/S4"));
      assertTrue(src(d,"Root/S2/t2").equals("Root/S2/S3"));
      assertTrue(dest(d,"Root/S2/t2").equals("Root/S2"));
   }

   @Test 
   public void srcDestFQN1() {
      DashModule d = test("srcDestFQN1");
      assertTrue(src(d,"Root/S1/t1").equals("Root/S1"));
      assertTrue(dest(d,"Root/S1/t1").equals("Root/S1/S7"));
      assertTrue(src(d,"Root/S2/S3/S4/t2").equals("Root/S2/S3/S4"));
      assertTrue(dest(d,"Root/S2/S3/S4/t2").equals("Root/S1/S7"));
   }
  
   @Test 
   public void paramSrcDest1() {
      DashModule d = test("paramSrcDest1");
      assertTrue(src(d,"Root/A/t1").equals("Root/A[p0_APID]"));
      assertTrue(dest(d,"Root/A/t1").equals("Root/A[p0_APID]"));      
   }   
   @Test 
   public void paramSrcDest2() {
      DashModule d = test("paramSrcDest2");
      assertTrue(src(d,"Root/A/t1").equals("Root/A[p0_APID]"));
      assertTrue(dest(d,"Root/A/t1").equals("Root/B/S1[x]"));      
   }  

   // getAllAnces --------------

   @Test 
   public void getAllAnces1() {
      DashModule d = test("noSrc1");
      assertTrue(d.getAllAnces("Root/S1").equals(ll(new String[]{"Root", "Root/S1"})));
   }

   // getClosestParamAnces ----------------

   @Test 
   public void getClosestParamAnces1() {
      DashModule d = test("noSrc1");
      assertTrue(d.getClosestParamAnces("Root/S1").equals("Root"));
      assertTrue(d.getClosestParamAnces("Root/S2").equals("Root"));
   }
   @Test 
   public void getClosestParamAnces2() {
      DashModule d = test("scopeParam2");
      assertTrue(d.getClosestParamAnces("Root/A/B/S1").equals("Root/A/B"));
      assertTrue(d.getClosestParamAnces("Root/A/B").equals("Root/A/B"));
   }



   // getRegion ----------------------
   @Test 
   public void getRegion1() {
      DashModule d = test("getRegion1");
      assertTrue(d.getRegion("Root/S1/S2")
         .equals(ll(new String[]{
            "Root", 
            "Root/S1", 
            "Root/S1/S2",
            "Root/S3",
            "Root/S3/S4", 
            "Root/S3/S4/S5",
            "Root/S3/A",
            "Root/S3/A/S7",
            "Root/S3/A/S7/S8",
            "Root/S3/B",
            "Root/S3/B/S7"
         })));
   }
   @Test 
   public void getRegion2() {
      DashModule d = test("getAllNonConcDesc1");
      assertTrue(d.getRegion("Root/S1/S2")
         .equals(ll(new String[]{
            "Root", 
            "Root/S1", 
            "Root/S1/S2",
            "Root/S3",
            "Root/S3/S4", 
            "Root/S3/S4/S5",
            "Root/S3/A",
            "Root/S3/A/S7",
            "Root/S3/B",
            "Root/S3/B/S7"
         })));
   }

   // allPrefixDashRefs ----------------------
   

    
   @Test
   public void allPrefixDashRefs1() {
      DashModule d = test("scopeParam1");
      assertTrue(
         allPrefixDashRefs(d,"Root/A/S1/t1")
         .equals(ll(new String[]{
            "Root",
            "Root/A[(p0_APID = x => p0_APID else APID)]"
         })));     
   }
   @Test
   public void allPrefixDashRefs2() {
      DashModule d = test("scopeParam2");
      assertTrue(
         allPrefixDashRefs(d, "Root/A/B/S1/t1")
         .equals(ll(new String[]{
            "Root",
            "Root/A[(p0_APID = x => p0_APID else APID)]",
            "Root/A/B[(p0_APID = x => p0_APID else APID), (AND[p0_APID = x, p1_BPID = y] => p1_BPID else BPID)]"
         })));     
   }
   @Test
   public void allPrefixDashRefs3() {
      DashModule d = test("scopeParam3");
      assertTrue(
         allPrefixDashRefs(d, "Root/A/B/S1/t1")
         .equals(ll(new String[]{
            "Root",
            "Root/A[p0_APID]",
            "Root/A/B[p0_APID, p1_BPID]"
         })));     
   }
   @Test
   public void allPrefixDashRefs4() {
      DashModule d = test("getEntered5");
      assertTrue(
         allPrefixDashRefs(d, "Root/S1/t1")
         .equals(ll(new String[]{
            "Root",
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
            "Root/S1",
            "Root/S2"
         })));
   }
   @Test 
   public void getLeafStatesExited2() {
      DashModule d = test("noSrc2");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1",
            "Root/S2/S3/S4"
         })));
   }
   @Test 
   public void getLeafStatesExited3() {
      DashModule d = test("noDefaultNeeded2");
      assertTrue(
         exited(d,"Root/C/t1")
         .equals(ll(new String[]{
            "Root/C"
         })));
   }
   @Test 
   public void getLeafStatesExited4() {
      DashModule d = test("noSrcDest1");
      assertTrue(
         exited(d,"Root/t1")
         .equals(ll(new String[]{
            "Root"
         })));
   }
   @Test 
   public void getLeafStatesExited5() {
      DashModule d = test("otherSrcDest1");
      assertTrue(
         exited(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S1",
            "Root/S2/S3/S4"
         })));
      assertTrue(
         exited(d,"Root/S2/t2")
         .equals(ll(new String[]{
            "Root/S2/S3/S4"
         })));
   }
   @Test 
   public void getLeafStatesExited6() {
      DashModule d = test("paramSrcDest1");
      assertTrue(
         exited(d,"Root/A/t1")
         .equals(ll(new String[]{
            "Root/A[p0_APID]"
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
         .equals("Root/A[(p0_APID = x => p0_APID else APID)]"));
   }
   @Test 
   public void getScope2() {
      DashModule d = test("scopeParam2");
      assertTrue(
         d.getScope("Root/A/B/S1/t1").toString()
         .equals("Root/A/B[(p0_APID = x => p0_APID else APID), (AND[p0_APID = x, p1_BPID = y] => p1_BPID else BPID)]"));
   }
   @Test 
   public void getScope3() {
      DashModule d = test("scopeParam3");
      assertTrue(
         d.getScope("Root/A/B/S1/t1").toString()
         .equals("Root/A/B[p0_APID, p1_BPID]"));
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
            "Root/S2"
         })));
   }
   @Test 
   public void getLeafStatesEntered2() {
      DashModule d = test("noSrc2");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/S3/S4"
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
            "Root/S2/A"
         })));
   }
   @Test 
   public void getLeafStatesEntered6() {
      DashModule d = test("getEntered6");
      assertTrue(
         entered(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3"
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

   // getLeafStatesEnteredInScope -----------------
   
   public List<String> enteredInScope(DashModule d, String tfqn) {
      return d.entered(tfqn)
         .stream()
         .map (i -> i.toString())
         .collect(Collectors.toList());
   } 

   @Test 
   public void getLeafStatesEnteredInScope1() {
      DashModule d = test("noSrc1");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope2() {
      DashModule d = test("getEnteredInScope2");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/B/S3",
            "Root/A/S2",
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope3() {
      DashModule d = test("getEntered5");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope4() {
      DashModule d = test("getEntered6");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope5() {
      DashModule d = test("getEntered7");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/S3[AID]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope6() {
      DashModule d = test("getEntered8");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]",
            "Root/S2/A/C[AID, CID]"
         })));
   }
   @Test 
   public void getLeafStatesEnteredInScope7() {
      DashModule d = test("getEntered9");
      assertTrue(
         enteredInScope(d,"Root/S1/t1")
         .equals(ll(new String[]{
            "Root/S2/A/B/S3[AID, BID]", 
            "Root/S2/A/C/S5[AID, CID]",
         })));
   }

   // connected tests on one model
   @Test
   public void overall1() {
      DashModule d = test("overall1");
      String tfqn = "Root/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/C/S2[c1]"));
      assertTrue(
         d.getScope(tfqn).toString().equals("Root"));
      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[AID, BID]", 
            "Root/C/S2[CID]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/C/S2[CID - c1]", 
            "Root/A/B/S1[AID, BID]", 
            "Root/C/S2[c1]"
         })));
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList()));
   }
   @Test
   public void overall2() {
      DashModule d = test("overall2");
      String tfqn = "Root/A/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[p0_AID, p1_BID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/S2[a2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(p0_AID = a2 => p0_AID else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(p0_AID = a2 => p0_AID else AID), BID]", 
            "Root/A/S2[(p0_AID = a2 => p0_AID else AID)]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S2[(p0_AID = a2 => p0_AID else AID) - a2]", 
            "Root/A/S2[a2]", 
         })));      
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(0,1)));
   }
   
   @Test
   public void overall3() {
      DashModule d = test("overall3");
      String tfqn = "Root/A/S2/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/S2[p0_AID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(p0_AID = a1 => p0_AID else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(p0_AID = a1 => p0_AID else AID), BID]", 
            "Root/A/S2[(p0_AID = a1 => p0_AID else AID)]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S2[(p0_AID = a1 => p0_AID else AID) - a1]",  
            "Root/A/B/S1[a1, BID - b1]", 
            "Root/A/B/S1[a1, b1]"
         })));      

      tfqn = "Root/A/B/S1/t2";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[p0_AID, p1_BID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B/S1[p0_AID, p1_BID]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A/B/S1[p0_AID, p1_BID]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[p0_AID, p1_BID]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[p0_AID, p1_BID]"
         }))); 

      tfqn = "Root/A/B/S1/t3";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[p0_AID, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B/S1[p0_AID, b2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A/B/S1[p0_AID, (b1 = b2 => b1 else BID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[p0_AID, (b1 = b2 => b1 else BID)]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[p0_AID, (b1 = b2 => b1 else BID) - b2]",
            "Root/A/B/S1[p0_AID, b2]"
         }))); 

   }

   @Test
   public void overall4() {
      DashModule d = test("overall4");
      String tfqn = "Root/A/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a1, b1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/S2[a2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A[(a1 = a2 => a1 else AID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a1 = a2 => a1 else AID), BID]", 
            "Root/A/S2[(a1 = a2 => a1 else AID)]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a1 = a2 => a1 else AID) - a2, BID]", 
            "Root/A/S2[a2]"
         })));      
   }   
   
   @Test
   public void overall5() {
      DashModule d = test("overall5");
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
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a1 = a2 => a1 else AID) - a2, BID]", 
            "Root/A/B/S1[a2, BID]",
         })));      

      tfqn = "Root/t2";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a3, b3]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B/S1[a4, b4]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A/B/S1[(a3 = a4 => a3 else AID), (AND[a3 = a4, b3 = b4] => b3 else BID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a3 = a4 => a3 else AID), (AND[a3 = a4, b3 = b4] => b3 else BID)]", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a3 = a4 => a3 else AID) - a4, BID]", 
            "Root/A/B/S1[a4, (AND[a3 = a4, b3 = b4] => b3 else BID) - b4]",
            "Root/A/B/S1[a4, b4]"
         })));     

      tfqn = "Root/t3";
      assertTrue(
         src(d, tfqn).equals("Root/A/B/S1[a5, b5]"));
      assertTrue(
         dest(d, tfqn).equals("Root/A/B[a6, b6]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/A/B[(a5 = a6 => a5 else AID), (AND[a5 = a6, b5 = b6] => b5 else BID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a5 = a6 => a5 else AID), (AND[a5 = a6, b5 = b6] => b5 else BID)]", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/B/S1[(a5 = a6 => a5 else AID) - a6, BID]", 
            "Root/A/B/S1[a6, (AND[a5 = a6, b5 = b6] => b5 else BID) - b6]",
            "Root/A/B/S1[a6, b6]"
         })));  
   }

   @Test
   public void overall6() {
      DashModule d = test("overall6");
      String tfqn = "Root/B/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/B/S1[p0_BID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/B[p0_BID]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/B[p0_BID]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/S1[p0_BID]", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/S1[p0_BID]",
         })));    

      tfqn = "Root/B/S1/t2";
      assertTrue(
         src(d, tfqn).equals("Root/B/S1[p0_BID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/B[b1]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/B[(p0_BID = b1 => p0_BID else BID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/S1[(p0_BID = b1 => p0_BID else BID)]", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/S1[(p0_BID = b1 => p0_BID else BID) - b1]",
            "Root/B/S1[b1]"
         })));  

      tfqn = "Root/B/S1/t3";
      assertTrue(
         src(d, tfqn).equals("Root/B/S1[p0_BID]"));
      assertTrue(
         dest(d, tfqn).equals("Root/C"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/C", 
            "Root/B/S1[BID]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/C"
         })));  

      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(0)));
   }

   @Test
   public void overall7() {
      DashModule d = test("overall7");
      String tfqn = "Root/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/S1"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/S1"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/S1", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/S1",
         }))); 

      tfqn = "Root/S1/t2";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/B"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A",
            "Root/B",
            "Root/C[CID]",
            "Root/S1", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A",
            "Root/C[CID]",
            "Root/B",
         }))); 

      tfqn = "Root/S1/t3";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/C[c1]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A",
            "Root/B",
            "Root/C[CID]",
            "Root/S1", 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/C[CID - c1]",
            "Root/A",
            "Root/B",
            "Root/C[c1]"
         }))); 

   }
   @Test
   public void overall8() {
      DashModule d = test("overall8");
      String tfqn = "Root/t1";
      assertTrue(
         src(d, tfqn).equals("Root/S3"));
      assertTrue(
         dest(d, tfqn).equals("Root/B/E/S2[e1]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S1[AID]",
            "Root/B/C",
            "Root/B/D",
            "Root/B/E/S2[EID]",
            "Root/B/E/S4[EID]",
            "Root/S3" 
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/A/S1[AID]",
            "Root/B/E/S4[EID - e1]",
            "Root/B/C",
            "Root/B/D",
            "Root/B/E/S2[e1]"
         }))); 
   }

   @Test
   public void overall9() {
      DashModule d = test("overall9");
      String tfqn = "Root/t1";
      assertTrue(
         src(d, tfqn).equals("Root/B/E/F[e1, f1]"));
      assertTrue(
         dest(d, tfqn).equals("Root/B/E/G[e2]"));
      assertTrue(
         d.getScope(tfqn).toString()
         .equals("Root/B/E[(e1 = e2 => e1 else EID)]"));      
      assertTrue(
         exited(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/E/S2[(e1 = e2 => e1 else EID)]", 
            "Root/B/E/S4[(e1 = e2 => e1 else EID)]",
            "Root/B/E/F[(e1 = e2 => e1 else EID), FID]",
            "Root/B/E/G[(e1 = e2 => e1 else EID)]"
         })));
      assertTrue(
         enteredInScope(d,tfqn)
         .equals(ll(new String[]{
            "Root/B/E/S4[(e1 = e2 => e1 else EID) - e2]",
            "Root/B/E/F[e2, FID]",
            "Root/B/E/G[e2]"
         }))); 
   }

   @Test
   public void overall10() {
      DashModule d = test("overall10");
      String tfqn = "Root/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/S2")); 
   }

   @Test
   public void overall11() {
      DashModule d = test("overall11");
      String tfqn = "Root/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/S2")); 
   }

   @Test
   public void overall12() {
      DashModule d = test("overall12");
      String tfqn = "Root/S1/t1";
      assertTrue(
         src(d, tfqn).equals("Root/S1"));
      assertTrue(
         dest(d, tfqn).equals("Root/S1/S7")); 
   }

   @Test 
   public void overall13() {
      DashModule d = test("overall13");
      String tfqn = "Root/A/B/t1";
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(0,1)));      
      tfqn = "Root/A/t2";
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(0)));   
      tfqn = "Root/C/t3";
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(2)));   
      tfqn = "Root/C/D/t4";
      assertTrue(
         d.getTransParamsIdx(tfqn)
         .equals(Arrays.asList(2,3))); 
      assertTrue(
         d.getAllParamsInOrder()
         .equals(Arrays.asList("AID","BID","BID","AID")));  
   }

   // priority
   @Test 
   public void pri1() {
      DashModule d = test("pri1");
      String tfqn = "Root/t1";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));

   }
   @Test 
   public void pri2() {
      DashModule d = test("pri2");
      String tfqn = "Root/t1";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));
     tfqn = "Root/A/t2";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/t1"
         })));
   }

   @Test 
   public void pri3() {
      DashModule d = test("pri3");
      String tfqn = "Root/t1";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));
      tfqn = "Root/t2";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));
     tfqn = "Root/t3";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/t1",
            "Root/t2"
         })));
   }

   @Test 
   public void pri4() {
      DashModule d = test("pri4");
      String tfqn = "Root/t1";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));
      tfqn = "Root/t2";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/t1"
         })));

   }

   @Test 
   public void pri5() {
      DashModule d = test("pri5");
      String tfqn = "Root/t1";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{})));
      tfqn = "Root/t2";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/t1"
         })));

   }

   @Test 
   public void pri6() {
      DashModule d = test("pri6");
      String tfqn = "Root/A/B/t1";
      
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/A/t2",
            "Root/t3"
         })));
      
      tfqn = "Root/A/t2";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
            "Root/t3"
         })));
      
      tfqn = "Root/t3";
      assertTrue(
         d.getHigherPriTrans(tfqn)
         .equals(ll(new String[]{
         })));
   }

}
