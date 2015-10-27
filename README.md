# Simple functional language

## Overview

The project implements interpreter created for a simple functional language. The interpreter was created using [The BNF Converter](https://github.com/BNFC/bnfc).

## Language grammar

Grammar of the language can be found here: [Fun.cf](src/Fun.cf). It is written using [the LBNF notation](https://bnfc.readthedocs.org/en/latest/lbnf.html).

You can find example programs written in this toy programming language in [the example directory](examples/). [The good directory](examples/good/) directory contains well-written programs and [the bad directory](examples/bad/) programs that returns an error.

## Usage

### 1. Install BNFC

You can find information on [the official site](http://bnfc.digitalgrammars.com/) and [the github page](https://github.com/BNFC/bnfc). The version that has been used during development is 2.8.

### 2. Run the bash script

```
./remake_grammar.sh
```

The script creates necessary files for later compilation. The script assumes that BNFC is visible in the environment, so it's vital that you haven't miss the previous step.

### 4. Use cabal to install

```
cabal install
```

### 5. Run with cabal

```
cabal run < examples/good/eg1.in
```

### Testing

```
cabal test
```
