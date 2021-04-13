#!/bin/bash

## ----------------------------------------------------------------------
##
## This script takes a parsing log and from it generates a human readable
## parsing trace, i.g.  a sequence of shifts and reduces that took place.
##
## To get the parsing log just set the "debug" environment variable to
## "yes" before runngin Alloy (or add "-Ddebug=yes" to the list of JVM
## arguments)
##
## This script must be invoked from exactly the folder where it resides
## because it needs to find the CompParser.java and CompSym.java files
## in the same folder. 
##
## ----------------------------------------------------------------------

logFile=$1

if [[ -z $logFile ]]
then
    echo "usage: $0 <log-file-name>"
    exit
fi

if [[ ! -f $logFile ]]
then
    echo "file $logFile doesn't exist" 
    exit
fi

while read line 
do
  if [[ ! -z $(echo $line | grep "^reduce ") ]]
  then
    act=$(echo $line | sed 's/reduce //')
    echo "reduce" 
    grep "case $act:" CompParser.java
  elif [[ ! -z $(echo $line | grep "^shift ") ]]
  then
    sym=$(echo $line | sed 's/shift //')
    sgn=$(grep " = $sym;" CompSym.java | sed 's/  public static final int //' | sed 's/ = '$sym';//')
    echo "shift"
    echo "          $sgn"
  else
    echo $line
  fi
done < $logFile