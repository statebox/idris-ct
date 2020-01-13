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

> module Monad.KleisliCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalTransformation
> import Monad.KleisliCategoryHelpers
> import Monad.Monad
>
> %access public export
> %default total
>
> kleisliCategory : {cat : Category} -> Monad cat -> Category
> kleisliCategory {cat} m = MkCategory
>   (obj cat)
>   (\a, b => mor cat a (mapObj (functor m) b))
>   (component (unit m))
>   (\a, b, c, f, g => compose cat _ _ _ (compose cat _ _ _ f (mapMor (functor m) _ _ g))
>                                        (component (multiplication m) c))
>   (kleisliCategoryLeftIdentity {cat} m)
>   (kleisliCategoryRightIdentity {cat} m)
>   (kleisliCategoryAssociativity {cat} m)
