#!/bin/bash

# The purpose of this script is to copy the Alloy files that we use
# but have to do some slight renaming in them
# rerun this script whenever Alloy updates these files

# /g means multiple places on line

# it's tricky when to convert to turn CompModule into DCModule (the original CompModule with renaming) 
# vs DashModule (our code, which is an extension of DCModule)

p=../../../../../../../../org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg/parser/
msg=$'/*\n * DO NOT EDIT THIS FILE\n * DASH: file copied from Alloy src with replacements for DashModule - see install-alloy-files.sh \n */\n\n'

# --------------
# the filter sits between the Lexer and the Parser - to get it to call our DashLexer, we have to make a copy of the file
cp $p/CompFilter.java .

sed -i -e 's/package edu.mit.csail.sdg.parser/package ca.uwaterloo.watform.parser/' CompFilter.java

sed -i -e 's/CompLexer/DashLexer/g' CompFilter.java
sed -i -e 's/CompModule/DashModule/g' CompFilter.java
sed -i -e 's/CompFilter/DashFilter/g' CompFilter.java
# just adding a comment to the line -- could delete this if comment not relevant anymore
# sed -i -e 's/L.alloy_module = module;/L.alloy_module = module; \/\/NAD: Tamjid had this line commented out/' CompFilter.java
{ echo "$msg"; cat CompFilter.java; } > DashFilter.java
rm CompFilter.java 

# --------------
cp $p/CompUtil.java .
# order matters here
sed -i -e 's/package edu.mit.csail.sdg.parser/package ca.uwaterloo.watform.parser/' CompUtil.java
#sed -i -e 's/import edu.mit.csail.sdg.parser.CompModule.Context;/import ca.uwaterloo.watform.parser.DCModule.Context;/' CompUtil.java
#sed -i -e 's/edu.mit.csail.sdg.parser.CompModule.Open/ca.uwaterloo.watform.parser.DCModule.Open/' CompUtil.java

# because resolveAll is done later for Dash processing
sed -i -e 's/return CompModule.resolveAll(rep == null ? A4Reporter.NOP : rep, root);/\/\/return CompModule.resolveAll(rep == null ? A4Reporter.NOP : rep, root);\n            return root; \/\/DASH: resolveAll is done later/' CompUtil.java

# careful to have space after this so we don't catch import edu.mit.csail.sdg.parser.Compodule.Open;
sed -i -e 's/CompModule /DashModule /g' CompUtil.java

# one place CompModule is used other than in types
sed -it -e 's/return new CompModule(null, "", "");/return new DashModule(null, "", "");/' CompUtil.java


sed -i -e 's/CompUtil/DashUtil/g' CompUtil.java

sed -i -e 's/CompParser/DashParser/g' CompUtil.java

sed -i -e 's/parseRecursively/parseRecursivelyDash/' CompUtil.java

sed -i -e 's/parseEverything_fromFile/parseEverything_fromFileDash/' CompUtil.java

sed -i -e 's/parseEverything_fromString/parseEverything_fromStringDash/' CompUtil.java

{ echo "$msg"; cat CompUtil.java; } > DashUtil.java

rm CompUtil.java 



rm *.java-e *.javat

# make DashModule an extension of DashCompModule 

