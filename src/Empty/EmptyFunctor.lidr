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

> module Empty.EmptyFunctor
>
> import Basic.Category
> import Basic.Functor
> import Empty.EmptyCategory
>
> %access public export
> %default total
> %auto_implicits off
>
> emptyMapObj : (cat : Category) -> obj emptyCategory -> obj cat
> emptyMapObj cat = void
>
> emptyMapMor :
>      (cat : Category)
>   -> (a, b : obj emptyCategory)
>   -> (f : mor emptyCategory a b)
>   -> mor cat (emptyMapObj cat a) (emptyMapObj cat b)
> emptyMapMor cat a b = void
>
> emptyFunctor : (cat: Category) -> CFunctor emptyCategory cat
> emptyFunctor cat = MkCFunctor
>   (emptyMapObj cat)
>   (emptyMapMor cat)
>   (\a => absurd a)
>   (\a => absurd a)
