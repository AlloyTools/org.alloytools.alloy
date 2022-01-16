# Dash: Declarative Abstract State hierarchy
---

Dash is a new language for the formal specification of abstract behavioural 
models, which combines the control-oriented constructs of statecharts with the 
declarative modelling of <a href="http://alloytools.org/" target="_blank">Alloy</a>.
From statecharts, Dash inherits a means to specify hierarchy, concurrency, and 
communication, three useful aspects to describe the behaviour of reactive systems.
From Alloy, Dash uses the expressiveness of relational logic and set theory to 
abstractly and declaratively describe structures, data, and operations.


This repository contains the code to build the Dash parser and translator and 
the <a href="http://http://dash.uwaterloo.ca:8080" target="_blank">website</a>
to convert a Dash model to Alloy and contains further documentation
about Dash.

# Integration with the Alloy API
---
This version of Dash aims to work alongside the existing Alloy API by making slight
modifications such that it is possible for the Alloy API to parse Dash models, check
for well-formedness conditions and convert a Dash model to an Alloy model for seamless 
model checking of Dash models using the Alloy Analyzer. 

The new Java files added to the Alloy API are described below:

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/Dash.cup:** This is the grammar file
for Dash. It is an extention to Alloy.cup (the grammar file for Alloy). The Dash.cup retains the grammar
for Alloy as it will need to parse Alloy expressions, signatures, functions, predicates, etc. Once the 
project is built using gradle, this file will be used by CUP to create the DashParser.java file and 
it will be responsible for parsing Dash models.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/Dash.lex:** This is the lexer file
for Dash. It is an extention to Alloy.lex (the lexer file for Alloy). The Dash.lex retains the Alloy tokens
as they will appear in a Dash model. Once the  project is built using gradle, this file will be used by JFlex
to create the DashLexer.java file to store the Dash/Alloy tokens.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashModule:** This is an extension of
of the AlloyModule file located within the same directory. This file performs the same tasks as the 
AlloyModule file, but it additionally builds the internal data structure for Dash models after they
have been parsed. This internal data structure is stored within containers inside the file, and is 
later accessed by other files that are responsible for converting a Dash model to an Alloy model

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashModuleToString:** This is used to print out
an Alloy AST after a CoreDash model has been converted to an Alloy AST. It will iterate through all the openers, signatures,
fucntions, predicates, commands in a DashModule containing an Alloy AST and print them to the console.
Any labels with paths will have paths removed (`this/name` becomes `name`) and the alloy string will be pretty printed.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser/DashValidation:** This is used to check
for well-formedness conditions of a Dash model. It is called immediately after the internal data structure
has been build and it makes sure that the parsed Dash model is correct i.e. two states in the same hierarchical level
do not have the same name, correct variable references, default states exist, etc.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/transform/DashToCoreDash:** This is used to convert the
internal Dash data structure in the DashModule and convert it to CoreDash. CoreDash expands transitions and modifies
commands within transitions such that it is easier to convert a Dash model to an Alloy model. It will largely modify
transitions stored inside the DashModule and create new transitions if necessary.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/ast:** This folder contains several new Dash AST files.
These are important for storing the required information regarding any parsed Dash model. These AST files will be
used by the DashParser when parsing a Dash model.

**org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/transform/CoreDashToAlloy:** This is used to create
an Alloy AST using a DashModule that is holding a CoreDash data structure. It will create the necessary Alloy 
ASTs such as signature, predicate, fact ASTs in order to tranform a CoreDash model to its respective Alloy model.
It will additionally create a command AST that will be used to build Alloy instances using Kodkod.

**org.alloytools.alloy.application/src/main/java/ca/uwaterloo/watform/dash4whole/Dash:** This is called by the
jar file in the command line. It takes in a .dsh file as an input, converts the Dash model to CoreDash and then
to an Alloy AST. The Alloy AST is stored in a DashModule object that contains that necessary signatures, predicates,
facts and commands needed to create an Alloy instance from the Alloy AST by passing the AST to Kodkod. 
Alloy makes use of a CompModule object to store the Alloy AST, but Dash uses a DashModule instead as functions 
within a CompModule are inaccessible. 

# Integration with Alloy Analyzer
---

The modifications to Alloy GUI files are described below:

**org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleGUI:**
- Added `doTranslate` to translate .dsh file and open a new tab with translated alloy. The corresponding translate button only appears when editing dash.
- Added `doNewDash()` for opening new tab in "dash mode" (currently unused)
- Modified `doRefreshRun()` to only display dash options in the run menu, and appropriately parse dash and log errors.
- Misc changes to add .dsh option when opening and saving files.

**org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/SimpleReporter:**
- Modified `SimpleTask1`'s run function to handle dash code.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/alloy4/OurSyntaxWidget:**
- Added `editingDash` field to indicate if the textbox is editing dash
- Misc changes to name add .dsh extension to untitled dash files

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/alloy4/OurTabbedSyntaxWidget:**
- Modified `newTab()` function to create new `OurSyntaxWidgets` in "Dash Mode"

# Building the project
---

In order to build the project, navigate to the

```org.alloytools.alloy```

directory in the command-line and then run the

```gradle build```

command. In the scenario that this command fails to build the project, please try

```./gradle build``` or ```./gradlew build``` or ```gradle build -x test```

Please note that ```gradle build -x test``` will not run the unit tests.

Once the build is successful, use the following command:

```java -jar org.alloytools.alloy.dashbuild/target/org.alloytools.alloy.dashbuild.jar```

This will give provide a prompt to speciy a path for a Dash (.dsh) file input and
an output path where the CoreDash print will be stored. Please specify the necessary
information, and a successful parse/validation of the input Dash model will result in
the printing of the CoreDash version of that model.




