#!/usr/bin/env bash
cd src
bnfc -m -haskell Fun.cf
make
cd ..