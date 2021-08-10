## Overview

Wiqed is a barebones theorem prover based on the calculus of constructions with support for definitions as presented in [Type Theory and Formal Proof](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C).

Note: This is a personal project to study the basic mechanisms that go into theorem provers like Coq. Wiqed is not production ready software.

## Installation

Wiqed is written in OCaml so you need a working installation of Ocaml and Opam.

Clone the repository

```
$ git clone https://github.com/felixmoebius/wiqed && cd wiqed
```

Install dependencies

```
$ opam install --deps-only
```

Build using dune

```
$ dune build
```

Or run the test suite

```
$ dune runtest
```

## Usage

You can invoke the wiqed executable by running

```
$ dune exec ./bin/wiqed.exe FILENAME
```

where `FILENAME` is the wiqed source file to be checked.

You can start by verifying the files in the [examples](./examples) folder.

```
$ dune exec ./bin/wiqed.exe examples/basic.wiqed
checking Simple...ok 
checking Simple_application...ok
checking Falsum...ok
checking Not...ok
checking Not_a_is_type...ok
checking And...ok
checking Imp...ok
checking Complex...ok
checking Complex_with_definition...ok
checking Nat...ok
done
```

Or

```
$ dune exec ./bin/wiqed.exe examples/fail.wiqed
checking Wrong...error
expected b
but infered type is a
```

## Documentation

There is no documentation available so far.

You may want to look at the [examples](./examples) and at the [grammar](./lib/parser.mly) for the wiqed language.