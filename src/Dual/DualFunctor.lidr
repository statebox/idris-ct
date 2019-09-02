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

> module Dual.DualFunctor
>
> import Basic.Category
> import Basic.Functor
> import Cats.CatsAsCategory as Cats
> import Dual.DualCategory
>
> %access public export
> %default total
>
> dualFunctor :
>      CFunctor cat1 cat2
>   -> CFunctor (dualCategory cat1) (dualCategory cat2)
> dualFunctor func = MkCFunctor
>   (mapObj func)
>   (\a, b => mapMor func b a)
>   (preserveId func)
>   (\a, b, c, f, g => preserveCompose func c b a g f)
>
> dualIsFunctorial : CFunctor Cats.catsAsCategory Cats.catsAsCategory
> dualIsFunctorial = MkCFunctor dualCategory (\a, b => dualFunctor) (\c => Refl) (\a, b, c, f, g => Refl)
