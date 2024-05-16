#!/bin/sh

BLOCKSIZE=8

devmpg --minimise --blocksize=$BLOCKSIZE -o src --split proof.json --devmdir="../../evm-dafny" weth.bin
