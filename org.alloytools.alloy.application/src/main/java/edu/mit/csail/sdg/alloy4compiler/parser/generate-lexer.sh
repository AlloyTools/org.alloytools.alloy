#!/bin/bash

java -cp $LIB_SDG/jars-external/JFlex.jar JFlex.Main --nobak -d . Alloy.lex

sed -i 's/public java_cup.runtime.Symbol next_token() throws java.io.IOException/public java_cup.runtime.Symbol next_token() throws java.io.IOException, Err/' CompLexer.java

