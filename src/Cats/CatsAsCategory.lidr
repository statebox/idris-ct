\iffalse
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
\fi

> module Cats.CatsAsCategory
>
> import Basic.Category
> import Basic.Functor
>
> %access public export
> %default total
>
> catsLeftIdentity :
>      (cat1, cat2 : Category)
>   -> (func : CFunctor cat1 cat2)
>   -> functorComposition cat1 cat1 cat2 (idFunctor cat1) func = func
> catsLeftIdentity cat1 cat2 func = functorEq
>   cat1
>   cat2
>   (functorComposition cat1 cat1 cat2 (idFunctor cat1) func)
>   func
>   (\a => Refl)
>   (\a, b, f => Refl)
>
> catsRightIdentity :
>      (cat1, cat2 : Category)
>   -> (func : CFunctor cat1 cat2)
>   -> functorComposition cat1 cat2 cat2 func (idFunctor cat2) = func
> catsRightIdentity cat1 cat2 func = functorEq
>   cat1
>   cat2
>   (functorComposition cat1 cat2 cat2 func (idFunctor cat2))
>   func
>   (\a => Refl)
>   (\a, b, f => Refl)
>
> catsAssociativity :
>      (cat1, cat2, cat3, cat4 : Category)
>   -> (func1 : CFunctor cat1 cat2)
>   -> (func2 : CFunctor cat2 cat3)
>   -> (func3 : CFunctor cat3 cat4)
>   -> functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3)
>    = functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3
> catsAssociativity cat1 cat2 cat3 cat4 func1 func2 func3 = functorEq
>    cat1
>    cat4
>    (functorComposition cat1 cat2 cat4 func1 (functorComposition cat2 cat3 cat4 func2 func3))
>    (functorComposition cat1 cat3 cat4 (functorComposition cat1 cat2 cat3 func1 func2) func3)
>    (\a => Refl)
>    (\a, b, f => Refl)
>
> catsAsCategory : Category
> catsAsCategory = MkCategory
>   Category
>   CFunctor
>   idFunctor
>   functorComposition
>   catsLeftIdentity
>   catsRightIdentity
>   catsAssociativity
