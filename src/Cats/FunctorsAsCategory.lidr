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

> module Cats.FunctorsAsCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
>
> %access public export
> %default total
>
> functorCategory : (cat1, cat2 : Category) -> Category
> functorCategory cat1 cat2 = MkCategory
>   (CFunctor cat1 cat2)
>   (NaturalTransformation cat1 cat2)
>   (idTransformation cat1 cat2)
>   (naturalTransformationComposition cat1 cat2)
>   (\fun1, fun2, (MkNaturalTransformation comp comm) =>
>     naturalTransformationExt cat1 cat2 fun1 fun2 _
>       (MkNaturalTransformation comp comm)
>       (\a => (leftIdentity _ _ _ _)))
>   (\fun1, fun2, (MkNaturalTransformation comp comm) =>
>     naturalTransformationExt cat1 cat2 fun1 fun2 _
>       (MkNaturalTransformation comp comm)
>       (\a => (rightIdentity _ _ _ _)))
>   (\fun1, fun2, fun3, fun4,
>     (MkNaturalTransformation comp1 comm1),
>     (MkNaturalTransformation comp2 comm2),
>     (MkNaturalTransformation comp3 comm3) =>
>       naturalTransformationExt cat1 cat2 fun1 fun4 _ _
>       (\a => associativity _ _ _ _ _ _ _ _))
