#!/bin/bash
export FM=$PWD/sources/SatELite/ForMani

cd sources/SatELite/SatELite
make r
cp SatELite_release ../../..

cd ../../glucose/core
make rs
cp glucose_static ../../..
 
