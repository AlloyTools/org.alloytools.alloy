package edu.mit.csail.sdg.alloy4whole;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashMap;
import java.util.Scanner;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.parser.DashModule;
import edu.mit.csail.sdg.parser.DashOptions;
import edu.mit.csail.sdg.parser.DashUtil;

public class Alloy {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String filePath = "D:/DashModels/Elevator1.dsh";//"D:/EHealth.als";//"D:/DashModels/EHealth.dsh";

        System.out.println("Please specify the CoreDash output location:");
        String outputDir = "D:/";

        if (!filePath.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
            //return;
        }
        sc.close();

        Path path = Paths.get(filePath);
        Path fileName = path.getFileName();
        DashOptions.outputDir = (outputDir + fileName);

        A4Reporter rep = new A4Reporter() {
            @Override
            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
                System.out.flush();
            }
        };

        boolean parse = true;

        if (parse) {

            System.out.println("Parsing Model");

            // Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking " + fileName + " =============");
            DashModule world = DashUtil.parseEverything_fromFileDash(rep, new LinkedHashMap<String,String>(), filePath);

            System.out.println("Parsing Successfully Completed!");
        }

    }
}