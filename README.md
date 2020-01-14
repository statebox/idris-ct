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

[![Build Status](https://travis-ci.com/statebox/idris-ct.svg?branch=master)](https://travis-ci.com/statebox/idris-ct) [![License: AGPL v3](https://img.shields.io/badge/License-AGPL%20v3-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)

# Idris category theory


This repository contains several definitions from category theory.

The project is written in [Idris](https://idris-lang.org/), which allows us to
state properties (logical propositions) of the code, along with their formal
proofs, in the code itself. These provide guarantees that the code is
correct by construction.

Moreover, we are using *literate* Idris, so that we can seamlessly integrate
code and documentation, and produce prose documentation alongside the compiled
artifacts.

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

If you get an error message like `error: cloning builder process: Operation not permitted`, run

```
sysctl kernel.unprivileged_userns_clone=1
```

as suggested in https://github.com/NixOS/nix/issues/2633

## Manual build

### Prerequisites

You'll need [lhs2tex](https://github.com/kosmikus/lhs2tex/blob/master/INSTALL), [latexmk](https://mg.readthedocs.io/latexmk.html) and [Idris](https://www.idris-lang.org/).

### Generate documentation

Use `make` to generate the PDF documentation. You will find it in the
`docs` directory.
Look directly in the [Makefile](Makefile) for additional options.

You can also consult the documentation directly [here](https://github.com/statebox/idris-ct-docs/blob/master/idris-ct-docs.pdf).

### Generate comparaison data with Idris2

Use `make compare` to output which files have not been converted to Idris2.

If the executable has already been generated, simply execute `./compare src/ idris2/` to rerun the
comparaison between the two file trees.


### Build code

You can build manually all the code using

```
idris --checkpkg idris-ct.ipkg
```

## Build with Elba

Alternatively you can build the library with [elba](https://github.com/elba/elba) using

```
elba build
```

## Use as a dependency

The preferred way to use this library as a dependency for another project is using [elba](https://github.com/elba/elba).

It should be enough to add the following section

```
[dependencies]
"statebox/idris-ct" = { git = "https://github.com/statebox/idris-ct" }
```

to the `elba.toml` file of your project.

### License

Unless explicitly stated otherwise all files in this repository are licensed under the GNU Affero General Public License.

Copyright © 2019 [Stichting Statebox](https://statebox.nl).
