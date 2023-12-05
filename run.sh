#!/bin/sh

TIMEOUT=120 #seconds
Z3_PATH="/home/djp/pkg/z3-4.8.5-x64-ubuntu-16.04/bin/z3"
#Z3_PATH="/home/djp/pkg/z3-4.12.2-x64-glibc-2.35/bin/z3"
#DAFNY_HOME="/home/djp/pkg/dafny-4.2.0/dafny"
DAFNY_HOME="/home/djp/pkg/dafny-4.3.0/dafny"
DAFNY_CMD="dafny verify --cores=8 --verification-time-limit=$TIMEOUT --solver-path=$Z3_PATH"
FILES=$(ls src/*.dfy)

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
