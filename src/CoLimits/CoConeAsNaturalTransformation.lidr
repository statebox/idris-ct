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

> module CoLimits.CoConeAsNaturalTransformation
>
> import Basic.Category
>
> import CommutativeDiagram.Diagram
> import Basic.NaturalTransformation
> import Basic.Functor
> import CoLimits.CoCone
>
> %access public export
> %default total
>
> Delta : (cat1, cat2 : Category) -> (n : obj cat2) -> CFunctor cat1 cat2
> Delta cat1 cat2 n = MkCFunctor
>   (\a => n)
>   (\a, b, f => identity cat2 n)
>   (\a => Refl)
>   (\a, b, c, f, g => sym (leftIdentity cat2 n n (identity cat2 n)))
>
> coConeToNaturalTransformation :
>      (index, cat : Category)
>   -> (dia : Diagram index cat)
>   -> (cocone : CoCone index cat dia)
>   -> NaturalTransformation index cat dia (Delta index cat (apex cocone))
> coConeToNaturalTransformation index cat dia cocone = MkNaturalTransformation
>   (\j => exists cocone j)
>   (\i, j, f => trans
>      (rightIdentity cat (mapObj dia i) (apex cocone) (exists cocone i))
>      (sym (commutes cocone i j f)))
