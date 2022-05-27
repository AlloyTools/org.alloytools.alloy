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
        // create velocity objects necessary for translation
        VelocityEngine ve = new VelocityEngine();
        ve.setProperty(RuntimeConstants.RESOURCE_LOADERS, "classpath");
        ve.setProperty("resource.loader.classpath.class", ClasspathResourceLoader.class.getName());
        ve.init();
        // Template t = ve.getTemplate("templates/VelocityTemplateFile.vm");    // the final template
        Template t = ve.getTemplate("templates/TestTemplateFile.vm");     // the template used to test
        VelocityContext vc = new VelocityContext();

        // add to template file

        // add signatures
        vc.put("basicSigLabels", dashPythonTranslation.basicSigLabels);

        // add concurrent states
        vc.put("concStateList", dashPythonTranslation.getStates());

        // print modified template file
        StringWriter sw = new StringWriter();
        t.merge(vc, sw);
        return sw.toString();
    }
}
