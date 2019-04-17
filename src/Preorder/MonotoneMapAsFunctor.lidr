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

> module Preorder.MonotoneMapAsFunctor
>
> import Basic.Category
> import Basic.Functor
> import Preorder.MonotoneMap
> import Preorder.PreorderAsCategory
> import Preorder.UniquePreorder
>
> -- contrib
> import Decidable.Order
>
> monotoneMapToFunctor : (UniquePreorder t1 po1, UniquePreorder t2 po2)
>   => MonotoneMap t1 po1 t2 po2
>   -> CFunctor (preorderAsCategory {t = t1} {po = po1}) (preorderAsCategory {t = t2} {po = po2})
> monotoneMapToFunctor {t1} {po1} {t2} {po2} (MkMonotoneMap fun fRespectsOrd) =
>   MkCFunctor
>     fun
>     fRespectsOrd
>     (\a => unique (fun a) (fun a) (fRespectsOrd a a (reflexive a)) (reflexive (fun a)))
>     (\a, b, c, f, g =>
>       unique (fun a) (fun c)
>         (fRespectsOrd a c (transitive a b c f g))
>         (transitive (fun a) (fun b) (fun c) (fRespectsOrd a b f) (fRespectsOrd b c g)))
