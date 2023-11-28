#!/bin/sh

BLOCKSIZE=8

devmpg --blocksize=$BLOCKSIZE -o proof --split proof.json --devmdir="../../evm-dafny" weth.bin
