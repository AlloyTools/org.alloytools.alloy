package ca.uwaterloo.watform.dash4whole;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashModuleToString;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.CoreDashToAlloy;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class Dash {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = "C:\\Users\\Tamjid Hossain\\Desktop\\Dash Processes Models\\Carousel2.dsh";
        String elevator = "E:\\Alloy Specification Language\\Models\\ElevProc36.als";
        //"C:\\Users\\Tamjid Hossain\\Desktop\\Dash Processes Models\\Elevator.dsh";
        //"C:\Users\Tamjid Hossain\Desktop\Dash Models Testing\\TestModel.dsh";

        //if (!actual.endsWith(".dsh")) {
        //    System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
        //    return;
        //}
        sc.close();

        Path path = Paths.get(actual);
        Path fileName = path.getFileName();
        Path directory = path.getParent();
        DashOptions.outputDir = (directory.toString() + '/' + fileName.toString().substring(0, fileName.toString().indexOf(".")) + "AST");
        if (directory.toString() != null)
            DashOptions.dashModelLocation = directory.toString();

        A4Reporter rep = new A4Reporter();

        boolean parse = true;

        if (parse) {

            System.out.println("Parsing Model");

            VizGUI viz = null;

            //Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking " + fileName + " =============");

            DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashModule coreDash = DashToCoreDash.transformToCoreDash(dash);
            DashModule alloy = CoreDashToAlloy.convertToAlloyAST(coreDash);
            alloy = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloy);
            DashModuleToString.toString(alloy);

            dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            coreDash = DashToCoreDash.transformToCoreDash(dash);
            alloy = CoreDashToAlloy.convertToAlloyAST(coreDash);
            alloy = DashModule.resolveAll(rep == null ? A4Reporter.NOP : rep, alloy);
            DashModuleToString.toString(alloy);
            //CompModule alloy = CompUtil.parseEverything_fromFile(rep, null, elevator);
            //CompModuleToString.toString(alloy, elevator);

            // Choose some default options for how you want to execute the
            // commands
            A4Options options = new A4Options();

            options.solver = A4Options.SatSolver.SAT4J;

            for (Command command : alloy.getAllCommands()) {
                // Execute the command
                System.out.println("============ Command " + command + ": ============");
                A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, alloy.getAllReachableSigs(), command, options);
                // Print the outcome
                System.out.println(ans);
                // If satisfiable...
                if (ans.satisfiable()) {
                    // You can query "ans" to find out the values of each set or
                    // type.
                    // This can be useful for debugging.
                    //
                    // You can also write the outcome to an XML file
                    ans.writeXML("alloy_example_output.xml");
                    //
                    // You can then visualize the XML file by calling this:
                    if (viz == null) {
                        viz = new VizGUI(false, "alloy_example_output.xml", null);
                    } else {
                        viz.loadXML("alloy_example_output.xml", true);
                    }
                }
            }

        }
    }
}
