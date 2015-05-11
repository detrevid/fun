# Simple functional language

## Overview

The project implements parser created for simple functional language. The parser was created with [The BNF Converter](https://github.com/BNFC/bnfc).

##Language grammar

Grammar of the language can be found under [Fun.cf](src/Fun.cf). It is written using [LBNF notation](https://bnfc.readthedocs.org/en/latest/lbnf.html).

You can find example programs written in this toy programming language in the [example directory](examples/).

##Usage

###1. Install BNFC

http://bnfc.digitalgrammars.com/download/

###2. Run bash script

```
./remake_grammar.sh
```

###4. Use cabal to install

```
cabal install 
```

###5. Run with cabal
```
cabal run < examples/good/eg1.in
```
