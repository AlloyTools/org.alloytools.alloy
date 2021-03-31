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

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/Dash.cup:** This is the grammar file
for Dash. It is an extention to Alloy.cup (the grammar file for Alloy). The Dash.cup retains the grammar
for Alloy as it will need to parse Alloy expressions, signatures, functions, predicates, etc. Once the 
project is built using gradle, this file will be used by CUP to create the DashParser.java file and 
it will be responsible for parsing Dash models.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/Dash.lex:** This is the lexer file
for Dash. It is an extention to Alloy.lex (the lexer file for Alloy). The Dash.lex retains the Alloy tokens
as they will appear in a Dash model. Once the  project is built using gradle, this file will be used by JFlex
to create the DashLexer.java file to store the Dash/Alloy tokens.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/DashModule:** This is an extension of
of the AlloyModule file located within the same directory. This file performs the same tasks as the 
AlloyModule file, but it additionally builds the internal data structure for Dash models after they
have been parsed. This internal data structure is stored within containers inside the file, and is 
later accessed by other files that are responsible for converting a Dash model to an Alloy model

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/DashValidation:** This is used to check
for well-formedness conditions of a Dash model. It is called immediately after the internal data structure
has been build and it makes sure that the parsed Dash model is correct i.e. two states in the same hierarchical level
do not have the same name, correct variable references, default states exist, etc.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/TransformCoreDash:** This is used to convert the
internal Dash data structure in the DashModule and convert it to CoreDash. CoreDash expands transitions and modifies
commands within transitions such that it is easier to convert a Dash model to an Alloy model. It will largely modify
transitions stored inside the DashModule and create new transitions if necessary.

**org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/TransformCoreDash:** This is used to convert the
internal Dash data structure in the DashModule and convert it to CoreDash. CoreDash expands transitions and modifies
commands within transitions such that it is easier to convert a Dash model to an Alloy model. It will largely modify
transitions stored inside the DashModule and create new transitions if necessary.




