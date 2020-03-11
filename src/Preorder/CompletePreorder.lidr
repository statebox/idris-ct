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

> module Preorder.CompletePreorder
>
> import Basic.Category
> import Basic.Functor
>
> %access public export
> %default total
>
> CompletePreorder : Type -> Category
> CompletePreorder t = MkCategory
>   t
>   (\a, b => ())
>   (\a => ())
>   (\a, b, c, f, g => ())
>   (\a, b, () => Refl)
>   (\a, b, () => Refl)
>   (\a, b, c, d, (), (), () => Refl)
>
> completePreorderMorphism : (f : a -> b) -> CFunctor (CompletePreorder a) (CompletePreorder b)
> completePreorderMorphism f = MkCFunctor
>   f
>   (\a, b, f => ())
>   (\a => Refl)
>   (\a, b, c, (), () => Refl)
>
> collapser : (cat : Category) -> cat `CFunctor` (CompletePreorder (obj cat))
> collapser cat = MkCFunctor
>   id
>   (\_, _, _ => ())
>   (\_ => Refl)
>   (\_, _, _, _, _ => Refl)
