package ca.uwaterloo.watform.transform;

import ca.uwaterloo.watform.parser.DashModule;
import ca.uwaterloo.watform.rapidDash.DashPythonTranslation;
import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.VelocityEngine;
import org.apache.velocity.runtime.RuntimeConstants;
import org.apache.velocity.runtime.resource.loader.ClasspathResourceLoader;

import java.io.StringWriter;

public class CoreDashToPython {
    static DashPythonTranslation dashPythonTranslation;

    public static DashPythonTranslation convertToPythonTranslation(DashModule module) {
        return new DashPythonTranslation(module);
    }

    public static String toString(DashPythonTranslation dashPythonTranslation) {
        // Create velocity objects necessary for translation
        VelocityEngine ve = new VelocityEngine();
        ve.setProperty(RuntimeConstants.RESOURCE_LOADERS, "classpath");
        ve.setProperty("resource.loader.classpath.class", ClasspathResourceLoader.class.getName());
        ve.init();
        Template t = ve.getTemplate("templates/VelocityTemplateFile.vm");
        VelocityContext vc = new VelocityContext();

        // Add to template file
        vc.put("basicSigLabels", dashPythonTranslation.basicSigLabels);

        //print modified template file
        StringWriter sw = new StringWriter();
        t.merge(vc, sw);
        return sw.toString();
    }
}
