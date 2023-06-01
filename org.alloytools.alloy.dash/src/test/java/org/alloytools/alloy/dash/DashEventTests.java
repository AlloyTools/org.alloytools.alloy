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

import ca.uwaterloo.watform.core.DashUtilFcns;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.mainfunctions.MainFunctions;

public class DashEventTests {

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

   public static String on(DashModule d, String s) {
      return DashUtilFcns.NoneStringIfNeeded(d.getTransOn(s));
   }

   public static String send(DashModule d, String s) {
      return DashUtilFcns.NoneStringIfNeeded(d.getTransSend(s));
   }

   @Test
   public void event1() {
      DashModule d = test("event1");
      String tfqn = "Root/t1";
      assertTrue(
         on(d, tfqn).equals("Root/ev1"));
      assertTrue(
         send(d, tfqn).equals("Root/ev1"));
   }

   @Test
   public void event2() {
      DashModule d = test("event2");
      String tfqn = "Root/t1";
      assertTrue(
         on(d, tfqn).equals("none"));
      assertTrue(
         send(d, tfqn).equals("none"));
   }

   @Test
   public void event3() {
      DashModule d = test("event3");
      String tfqn = "Root/t1";
      assertTrue(
         on(d, tfqn).equals("Root/ev1"));
      assertTrue(
         send(d, tfqn).equals("none"));
   }

   //TODO add many more tests

}