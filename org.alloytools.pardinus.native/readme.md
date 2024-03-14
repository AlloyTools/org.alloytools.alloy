# Alloy Native code

This project contains the native code solvers for Pardinus. 

Native code sucks. The problem is that we need to build code for each supported platform. We support
the following platforms:

* linux/amd64
* windows/amd64
* darwin/amd64
* darwin/arm64

We follow the target naming convention of the _go_ language.

Both Linux and Windows can be build via docker container but this is not possible for the darwin (macos) code. This
requires an amd64 or arm64 mac. We therefore require that the code is build on a Mac.

The JAR that we build with bnd has the following layout:

* `native/...` – Contains the native directories in `os/arch/lib|exe` format.
* `services/kodkod.engine.satlab.SATFactory` – Contains a list of all the SATFactory classes in this bundle
* `org/alloytools/solvers/natv/...` – The class files for the included SATFactory's
* `LICENSE` – The licenses for the included files

The `natives` directory is stored in GIT. It is build by a Makefile in satsolvers on a Mac.

## Native Solver

To simplify the build, it helps when the names are consistently used. For each native solver, you need to pick a 
unique id like minisat, minisatprover, plingeling, etc.

To include a native solver first make sure there is a repository of the solver code in the Alloytools organization
with the name of the chosen id.  This repository can be cloned or contain a copy of the code. 

Make a branch `alloy`. This can be identical to `master` or it can contain any patches necessary to make the code 
work WITHOUT WARNINGS in our build.

In the src/main/java directory create a SATFactory for your solver. You can either make a JNI (hard work) or
an executable. Note, for JNI, the name of the class in upper case is the name of the library after mapping. E.g.
MiniSatProver will look for `libminisatprover.so` on linux, `libminisatprover.dylib` on darwin, and
`minisatprover.dll`. (I told you native code sucks.)

In satsolvers, make a directory for the native solver with the given id. This directory will contain a copy of the
repository for the native code in the `repo` directory. It will contain the JNI c or C++ file and a CMakeLists.txt
file.

## Building the natives

The workhorse is the Makefile in the satsolvers directory. I highly recommend to not clean it up ... Initially it
was started as a nice small clean Makefile with lots of loops. However, there are too many irregularities
that make a nice Makefile quite nasty in practice. The way it is now it is easy to make small exceptions
when the real world requires it.

The Makefile will build a selected set of native solvers for darwin/arm64 and darwin/amd64. A number of hours
were lost to compile it for darwin/arm64e so it is advised to not try this again.

The build for windows and linux is handled through [dockcross][1]. Dockcross is made in heaven. It provides
complete toolchains for builds. Initially it can create a shell file that starts docker, mounts the local
directory, and then runs a command in the container. See `dockcross_windows` file.

Although it would be nicer to be able to build the executables one by one, this was not done by the Makefile
because of performance. The darwin/arm64 environment needs to emulate the dockross docker container and 
the windows version need to build the zlib package. The overhead made it unbearably slow so we build
all the supported natives in one invocation.

[1]: https://github.com/dockcross/dockcross
