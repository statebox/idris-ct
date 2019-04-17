<!--
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
-->

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

### License

Unless explicitly stated otherwise all files in this repository are licensed under the GNU Affero General Public License.

Copyright © 2019 [Stichting Statebox](https://statebox.nl).
