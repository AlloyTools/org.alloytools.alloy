package edu.mit.csail.sdg.alloy4whole;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CoreDashToAlloy;
import edu.mit.csail.sdg.parser.DashModule;
import edu.mit.csail.sdg.parser.DashOptions;
import edu.mit.csail.sdg.parser.DashToCoreDash;
import edu.mit.csail.sdg.parser.DashUtil;

public class Alloy {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = "D:/DashModels/testdsh.dsh";//"D:/test.als";//"D:/EHealth.als";//"D:/DashModels/EHealth.dsh";
        String expected = "D:/DashModels/test.dsh";

        System.out.println("Please specify the CoreDash output location:");
        String outputDir = "D:/";

        if (!actual.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
            //return;
        }
        sc.close();

        Path path = Paths.get(actual);
        Path fileName = path.getFileName();
        DashOptions.outputDir = (outputDir + fileName);

        A4Reporter rep = new A4Reporter();

        boolean parse = true;

        if (parse) {

            System.out.println("Parsing Model");

            //Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking " + fileName + " =============");
            //Module world = CompUtil.parseEverything_fromFile(rep, null, filePath);

            //DashModule dashExpected = DashUtil.parseEverything_fromFileDash(rep, null, expected);

            DashModule dashActual = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashToCoreDash.transformToCoreDash(dashActual);
            CoreDashToAlloy.convertToAlloyAST(dashActual);
            dashActual = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, dashActual);

            //System.out.println("Expected Expr: " + dashExpected.facts.get(0).b.toString());
            System.out.println("Actual Expr: " + dashActual.facts.get(0).b.toString());

        }
    }
}


/*
 * for (String func : dashExpected.funcs.keySet()) { if (func.contains("path"))
 * { System.out.println("Expected Expr: " +
 * dashExpected.funcs.get(func).get(0).body + " Type: " +
 * dashExpected.funcs.get(func).get(0).body.getClass()); } } for (String func :
 * dashActual.funcs.keySet()) { if (func.contains("path")) {
 * System.out.println("Actual Expr  : " + dashActual.funcs.get(func).get(0).body
 * + " Type: " + dashActual.funcs.get(func).get(0).body.getClass()); } }
 */
