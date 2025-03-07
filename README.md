![Logo](https://avatars3.githubusercontent.com/u/30268214?v=4&s=200)
![Release build](https://github.com/alloytools/org.alloytools.alloy/actions/workflows/release.yml/badge.svg)
![Snapshot build](https://github.com/alloytools/org.alloytools.alloy/actions/workflows/snapshot.yml/badge.svg)


# Alloy

Alloy 6 is a self-contained executable, which includes an extended version of 
the Kodkod model finder and a variety of SAT solvers, as well as the standard
Alloy library and a collection of tutorial examples. The same jar file can be
incorporated into other applications to use Alloy as an API, and includes the
source code. See the release notes for details of new
features. 

Alloy 6 is a [major new release](http://alloytools.org/alloy6.html) More documentation can be found at: http://alloytools.org/documentation.html.

# Requirements

Alloy runs on all operating systems with a recent JVM (Java 17 or later). 
It is made available as a runnable jar file with both a cross-platform SAT solver
([Sat4j](http://www.sat4j.org/) and more efficient native SAT solvers ([minisat](http://minisat.se), [lingeling/plingeling](http://fmv.jku.at/lingeling/), [glucose](http://www.labri.fr/perso/lsimon/glucose/)).

# TL;DR

Checkout the project and type `./gradlew build`. You find the executable JAR in org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar after the build has finished.

     $ java -version           # requires Java 17
     openjdk version "17.0.9" 2023-10-17 LTS
     OpenJDK Runtime Environment (build 17.0.9+11-LTS)
     OpenJDK 64-Bit Server VM (build 17.0.9+11-LTS, mixed mode, sharing)
     $ git clone --recursive https://github.com/AlloyTools/org.alloytools.alloy.git
     $ cd org.alloytools.alloy
     $ ./gradlew build
     $ java -jar org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar
     # opens GUI
     
Note: if you are behind a proxy, the call to `gradlew` is likely to fail, unless you pass it further options about the http and https proxies (and possibly your login and password on this proxy). There are several ways to pass these options, a simple one is to type (replace the `XXXXX`'s by the adequate settings):

     $ ./gradlew -Dhttps.proxyHost=XXXXX -Dhttp.proxyHost=XXXXX -Dhttp.proxyPort=XXXXX \
          -Dhttps.proxyPort=XXXXX -Dhttp.proxyUser=XXXXX -Dhttp.proxyPassword=XXXXX \
          -Dhttps.proxyUser=XXXXX -Dhttps.proxyPassword=XXXXX \
          build

## Building Alloy

The Alloy build is using a _bnd workspace_ setup using a maven layout. This means it can be build  with Gradle and  the Eclipse IDE for interactive development. Projects are setup to continuously deliver the executable.

### Projects

The workspace is divided into a number of projects:

* [cnf](cnf) – Setup directory. Dependencies are specified in [cnf/central.xml] using the maven POM layout
* [org.alloytools.alloy.application](org.alloytools.alloy.application) – Main application code includes the parser, ast, visualiser, and application code
* [org.alloytools.alloy.dist](org.alloytools.alloy.dist) – Project to create the distribution executable JAR
* [org.alloytools.alloy.extra](org.alloytools.alloy.extra) – Models and examples
* [org.alloytools.pardinus](org.alloytools.pardinus) – A Kodkod extension without native code
* [org.alloytools.kodkod.nativesat](org.alloytools.kodkod.nativesat) – The native code libraries for Kodkod

### Relevant Project files

This workspace uses bnd. This means that the following have special meaning:

* [cnf/build.bnd](cnf/build.bnd) – Settings shared between projects
* ./bnd.bnd – Settings for a project. This file will _drag_ in code in a JAR.
* [cnf/central.mvn](cnf/central.mvn) – Dependencies from maven central

### Eclipse

The workspace is setup for interactive development in Eclipse with the Bndtools plugin. Download [Eclipse](https://www.eclipse.org/downloads/) and install it. You can then `Import` existing projects from the Git workspace. You should be asked to install Bndtools from the market place. You can also install Bndtools directly from the [Eclipse Market](https://marketplace.eclipse.org/content/bndtools) place (see `Help/Marketplace` and search for `Bndtools`). 

Bndtools will continuously create the final executable. The projects are setup to automatically update when a downstream project changes.

### IntelliJ IDEA (Ultimate Edition only)

Ensure you have the [Osmorc] plugin is enabled, as this plugin is needed for
Bndtools support. It should be enabled by default.

1. Choose `Import project from existing Sources` by using `Ctrl + Shift + a`.
2. Select the root folder (default folder name is `org.alloytools.alloy`).
3. Choose "Import project from external model: Bnd/Bndtools" and click "Next"
4. For "Select Bnd/Bndtools project to import", all projects should be checked by default, click "Next"
5. For project SDK, Choose "17", Click Finish
6. Select folder `org/alloytools/kodkod/nativesat/jni` as `Resource Folder` by selecting module `org.alloytools.kodkod.nativesat`, selecting folder `jni` -> `right click` -> `Mark Directory As` -> `Resource Root`.

Note: do *not* link the Gradle project, as this will prevent you from running
Alloy within IDEA.

To run the Alloy GUI within IDEA, navigate to
org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleGUI and run the SimpleGUI class.

[Osmorc]: https://plugins.jetbrains.com/plugin/1816-osmorc


### Gradle 

In the root of this workspace type `./gradlew`. This is a script that will download the correct version of gradle and run the build scripts. For settings look at [gradle.properties] and [settings.gradle].

### Continuous Integration

The workspace is setup to build after every commit using Github Actions, see [workflows](.github/workflows). 

It releases snapshots to `https://oss.sonatype.org/content/repositories/snapshots/org/alloytools/` for every CI build.

### Building the DMG file for OSX systems

Currently only the executable jar in org.alloytools.alloy.dist/target/org.alloytools.alloy.dist.jar is build. See the conveyor directory for the release executables.

## CONTRIBUTIONS

Please read the [CONTRIBUTING](CONTRIBUTING.md) to understand how you can contribute.
