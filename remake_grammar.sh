#!/usr/bin/env bash
cd src
bnfc -m --haskell -p Fun.BNFC Fun/Fun.cf
make
cd ..
