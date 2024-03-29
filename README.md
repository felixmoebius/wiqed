# Wiqed

![CI](https://github.com/felixmoebius/wiqed/actions/workflows/workflow.yml/badge.svg)

## Overview

Wiqed is a barebones theorem prover based on the calculus of constructions with support for definitions as presented in [Type Theory and Formal Proof](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C).

The implementation uses a _locally nameless representation_ as presented [here](https://repository.upenn.edu/cgi/viewcontent.cgi?article=1394&context=cis_papers), but extended to work with the calculus of constructions and definitions.
The relevant parts of the type checker can be found in [kernel.ml](./lib/kernel.ml) and [term.ml](./lib/term.ml).

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
but inferred type is a
```

## Tracing

Wiqed outputs the complete type derivation for each definition if you pass the `-trace` flag,
where the leading number corresponds to the depth of the judgement in the derivation tree.

```
dune exec -- ./bin/wiqed.exe examples/trace.wiqed -trace 
checking Apply_f_to_x
(0) f: (Pi a . b), x: a, b: *, a: * |- (f x)
(1) f: (Pi a . b), x: a, b: *, a: * |- f
(2) x: a, b: *, a: * |- (Pi a . b)
(3) x: a, b: *, a: * |- a
(4) b: *, a: * |- a
(5) a: * |- *
(6) |- *
(6) |- *
(5) a: * |- a
(6) |- *
(4) b: *, a: * |- a
(5) a: * |- *
(6) |- *
(6) |- *
(5) a: * |- a
(6) |- *
(3) @2: a, x: a, b: *, a: * |- b
(4) x: a, b: *, a: * |- a
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(4) x: a, b: *, a: * |- b
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(5) b: *, a: * |- b
(6) a: * |- *
(7) |- *
(7) |- *
(1) f: (Pi a . b), x: a, b: *, a: * |- x
(2) x: a, b: *, a: * |- (Pi a . b)
(3) x: a, b: *, a: * |- a
(4) b: *, a: * |- a
(5) a: * |- *
(6) |- *
(6) |- *
(5) a: * |- a
(6) |- *
(4) b: *, a: * |- a
(5) a: * |- *
(6) |- *
(6) |- *
(5) a: * |- a
(6) |- *
(3) @2: a, x: a, b: *, a: * |- b
(4) x: a, b: *, a: * |- a
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(4) x: a, b: *, a: * |- b
(5) b: *, a: * |- a
(6) a: * |- *
(7) |- *
(7) |- *
(6) a: * |- a
(7) |- *
(5) b: *, a: * |- b
(6) a: * |- *
(7) |- *
(7) |- *
(2) x: a, b: *, a: * |- x
(3) b: *, a: * |- a
(4) a: * |- *
(5) |- *
(5) |- *
(4) a: * |- a
(5) |- *
...ok
done
```

## Documentation

There is no documentation available so far.

You may want to look at the [examples](./examples) and at the [grammar](./lib/parser.mly) for the wiqed language.
