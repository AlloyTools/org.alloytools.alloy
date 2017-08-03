#!/bin/bash

java -cp $LIB_SDG/jars-external/java-cup-11a.jar java_cup.Main \
 -package edu.mit.csail.sdg.alloy4compiler.parser \
 -parser CompParser \
 -progress -time -compact_red \
 -symbols CompSym < Alloy.cup