#!/bin/bash

# tmp while working on grammar/parser

# copy DashFilter.java, DashUtil.java
cd org.alloytools.alloy.dash/src/main/java/ca/uwaterloo/watform/parser
./install-alloy-files.sh
cd ../../../../../../../../

# build Dash.cup, Dash.lex
cd org.alloytools.alloy.dash/parser
./install-alloy-files.sh
cd ../..

./gradlew build
