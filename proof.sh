#!/bin/sh

BLOCKSIZE=8

devmpg --minimise --masks --blocksize=$BLOCKSIZE -o src --split proof.json --devmdir="../../evm-dafny" weth.bin
