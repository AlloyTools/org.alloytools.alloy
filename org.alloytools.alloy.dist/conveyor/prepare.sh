#!/bin/bash
#
# Unfortunately, conveyor does not extract binaries from the JAR file
# and signs them. This script creates a new JAR file with the native directory
# removed and copies the natives to a separate directory. The conveyor script
# incldues the appropriate native files in the Resources directory. These
# will then automatically be signed.
# For testing purposes, this script also sets the executable bit on the native files.
#
# The new JAR file and native directory are placed in the `build` directory.
# IN = ../target/org.alloytools.alloy.dist.jar
# OUT = build/org.alloytools.alloy.dist.jar & build/native/
# 

set -e
#set -x

if [ "$#" -ne 0 ]; then
  echo "Usage: $0"
  exit 1
fi

IN=$(realpath ../target/org.alloytools.alloy.dist.jar)
BLD=$(realpath build)
TMP=$(mktemp -d)
SN=`basename $IN`
OUT=$BLD/$SN

rm -rf "$BLD"
mkdir -p "$BLD/"
cd "$TMP"
unzip "$IN"
mv native "$BLD/"
rm -rf native
zip -qr "$OUT" .
cd -
rm -rf "$TMP"
find "$BLD"/native/ -type f -exec chmod a+x {} \; 
echo "Prepared $OUT with native directory at $NAT"
