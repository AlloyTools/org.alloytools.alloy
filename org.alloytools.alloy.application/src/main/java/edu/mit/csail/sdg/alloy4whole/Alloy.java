package edu.mit.csail.sdg.alloy4whole;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

import ca.uwaterloo.watform.parser.CoreDashToAlloy;
import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashToCoreDash;
import ca.uwaterloo.watform.parser.DashToStringAlloyAST;
import ca.uwaterloo.watform.parser.DashUtil;
import edu.mit.csail.sdg.alloy4.A4Reporter;

public class Alloy {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = "D:/DashModels/testdshHie.dsh";//"D:/test.als";//"D:/EHealth.als";//"D:/DashModels/EHealth.dsh";
        String expected = "D:/JavaAlloy.als";

        System.out.println("Please specify the CoreDash output location:");
        String outputDir = "D:/Java.als";

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

            DashModule dashExpected = DashUtil.parseEverything_fromFileDash(rep, null, expected);

            DashModule dashActual = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashToCoreDash.transformToCoreDash(dashActual);
            CoreDashToAlloy.convertToAlloyAST(dashActual);

            dashExpected = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, dashExpected);

            DashToStringAlloyAST.printAlloyModel(dashExpected);
        }
    }
}

