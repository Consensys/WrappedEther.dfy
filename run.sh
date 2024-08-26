#!/bin/sh

TIMEOUT=120 #seconds
Z3_ROOT="/home/djp/pkg"
# Z3_VERSION="z3-4.8.5"
# Z3_VERSION="z3-4.12.2"
# Z3_VERSION="z3-4.12.3"
Z3_VERSION="z3-4.12.4"
#
# DAFNY_VERSION="4.2.0"
#DAFNY_VERSION="4.3.0"
DAFNY_VERSION="4.4.0"
#DAFNY_VERSION="4.5.0"
#DAFNY_VERSION="4.6.0"

#------------------------------------
echo "Dafny: $DAFNY_VERSION"
echo "Z3: $Z3_VERSION"
Z3_PATH="$Z3_ROOT/$Z3_VERSION/bin/z3"
DAFNY_HOME="/home/djp/pkg/dafny-$DAFNY_VERSION"
DAFNY_CMD="time $DAFNY_HOME/dafny verify --cores=8 --verification-time-limit=$TIMEOUT --solver-path=$Z3_PATH"
FILES=$(ls src/weth_*.dfy)

if [ $# -eq 0 ];
then
    echo "Verifying all files."
    for f in $FILES
    do
        echo "Verifying $f..."
        $DAFNY_CMD $f
    done
else
    echo "Verifing $1..."
    $DAFNY_CMD $1    
fi
