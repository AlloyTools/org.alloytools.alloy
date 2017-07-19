# Alloy

Alloy 4 is a self-contained executable, which includes the Kodkod
model finder and a variety of SAT solvers, as well as the standard
Alloy library and a collection of tutorial examples. The same jar file
can be incorporated into other applications to use Alloy as an API,
and includes the source code. See the release notes for details of new
features. To execute, simply double-click on the jar file, or type
java -jar alloy4.jar in a console.

More documentation can be found at: http://alloy.mit.edu/alloy/documentation.html.

## Building Alloy

### Building the JAR file

 - Always run the mkdist.sh script to create a distribution version of
   Alloy (instead of e.g. compiling/building from Eclipse)

   IMPORTANT: always run this script from the ALLOY_HOME folder, that
              is, the folder in which the mkdist.sh script is located.

 - The mkdist.sh script performs two tasks: (1) compiles Alloy, and
   (2) builds a JAR file that includes all external libraries etc.  If
   invoked with no parameters, it performs these two tasks in
   succession; individual tasks can be invoked by running "./mkdist.sh
   compile" and "./mkdist.sh dist" respectively. 

#### Compiling Alloy sources
 
 - the script first deletes everything from the "bin" folder   

 - the sources from the "src" folder are then compiled; target JVM
   version is set to 1.5 (important for MacOS!).  Version number and
   build date are also properly set (compiling from Eclipse won't do
   that automatically).  The compiled class files are placed in the
   "bin" folder.

   IMPORTANT: the script assumes that Kodkod has already been compiled
              and that the compiled binaries are located in $KODKOD_HOME/bin.

 - for the CLASSPATH, all JAR files found in the "lib" folder are
   automatically used, as well as the compiled Kodkod classes fro m
   $KODKOD_HOME/bin.

#### Making a distribution JAR file

 - Alloy ships as a single JAR file, meaning that all required
   external libraries are first individually unpacked and their
   contents are then repackaged together in a single JAR file.

 - all JAR files found in the "lib" folder are first unzipped into a
   single folder.

   NOTE: Currently, there are two JAR files in the "lib" folder: (1)
         apple-osx-ui.jar, and (2) extra.jar.  The first one contains
         necessary for the GUI to look nice on OSX operating systems.
         The second one contains all the GUI resources (images, icons,
         etc.), SAT native binaries for several different operating
         systems, licenses, example models, utility models, etc.

   CONSEQUENCE: If a sample model is changed for example, it is not
                enough to update the alloy file in the "models"
                folder, but it is also necessary to update the
                "extra.jar" file with the new model.

 - Kodkod binaries (from $KODKOD_HOME/bin/) are copied next.

 - Alloy binaries (from bin/) are copied afterwards. 

 - MANIFEST.MF is copied into the META-INF folder last.

 - finally, everything is zipped together and saved in a JAR file,
   namely dist/alloy-dev.jar.

### Building the DMG file for OSX systems

 - copy the "OSX-DMG-build" folder to some machine running OSX
 
 - create an .app file from the JAR file you built in the previous
   step (e.g. using "Jar Bundler" application for Mac).  During this
   process, specify that the icon file should be the
   "OSX-DMG-build/AlloyLogo.icns" file.

 - replace the existing .app file from the "OSX-DMG-build/dist" folder
   with the newly created one.

 - to create a DMG image, change directory to OSX-DMG-build and run
   the "build-dmg.sh" script. 
