package ca.uwaterloo.watform.dash4whole;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import ca.uwaterloo.watform.transform.CoreDashToPython;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Scanner;

public class RapidDash {

    @SuppressWarnings("resource" )
    public static void main(String args[]) throws Exception {

        System.out.println("Please specify the .dsh file path:");
        Scanner sc = new Scanner(System.in);
        String actual = sc.nextLine();

        if (!actual.endsWith(".dsh")) {
            System.err.println("File not supported.\nExpected a Dash file with 'dsh' extension");
            return;
        }
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

            //Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking " + fileName + " =============");

            DashModule dash = DashUtil.parseEverything_fromFileDash(rep, null, actual);
            DashModule coreDash = DashToCoreDash.transformToCoreDash(dash);
            // Start our translation from here
            DashPythonTranslation dashPythonTranslation = CoreDashToPython.convertToPythonTranslation(coreDash);
            System.out.println(CoreDashToPython.toString(dashPythonTranslation));
        }
    }
}