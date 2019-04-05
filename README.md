# Idris category theory

[![Build Status](https://travis-ci.com/statebox/idris-ct.svg?branch=master)](https://travis-ci.com/statebox/idris-ct)

This repository contains several definitions from category theory.

The code is written in [Idris](https://idris-lang.org/), which allows us to write explicitly properties and proofs.

We are actually using literate Idris, so that we can integrate seamlessly code
and documentation.

If you want a more detailed and slow introduction to the library, please have a look at the series of blog posts we are writing:

- https://blog.statebox.org/fun-with-categories-70c64649b8e0
- https://blog.statebox.org/concrete-categories-af444d5f055e
- https://blog.statebox.org/fun-with-functors-95e4e8d60d87

## Nix build

If you have [Nix](https://nixos.org/nix/) installed, you can build the project just by doing

```
nix-build
```

For additional targets, have a look at the instructions in [default.nix](default.nix).

## Manual build

### Prerequisites

You'll need

- [lhs2tex](https://github.com/kosmikus/lhs2tex/blob/master/INSTALL)
- [latexmk](https://mg.readthedocs.io/latexmk.html)
- [Idris](https://www.idris-lang.org/).

### Generate documentation

Use `make` to generate the PDF documentation. You will find it in the
`docs` directory.
Look directly in the [Makefile](Makefile) for additional options.

### Build code

You can build manually all the code using

```
idris --checkpkg idris-ct.ipkg
```

### Build with Elba

Alternatively you can build the library with [elba](https://github.com/elba/elba) using

```
elba build
```
