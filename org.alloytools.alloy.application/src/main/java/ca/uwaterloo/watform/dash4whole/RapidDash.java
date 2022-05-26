package ca.uwaterloo.watform.dash4whole;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.parser.DashModuleToString;
import ca.uwaterloo.watform.parser.DashOptions;
import ca.uwaterloo.watform.parser.DashUtil;
import ca.uwaterloo.watform.transform.DashToCoreDash;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.VelocityEngine;
import org.apache.velocity.runtime.RuntimeConstants;
import org.apache.velocity.runtime.resource.loader.ClasspathResourceLoader;

import java.io.StringWriter;
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

            // Create velocity objects necessary for translation
            VelocityEngine ve = new VelocityEngine();
            ve.setProperty(RuntimeConstants.RESOURCE_LOADERS, "classpath");
            ve.setProperty("resource.loader.classpath.class", ClasspathResourceLoader.class.getName());
            ve.init();
            Template t = ve.getTemplate("templates/VelocityTemplateFile.vm");
            VelocityContext vc = new VelocityContext();

            //print modified template file
            StringWriter sw = new StringWriter();
            t.merge(vc, sw);
            System.out.println(sw);

        }
    }
}