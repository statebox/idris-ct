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

> module Product.ProductFunctor
>
> import Basic.Category
> import Basic.Functor
> import Product.ProductCategory
> import Utils
>
> %access public export
> %default total
>
> productFunctor :
>      CFunctor cat1 cat2
>   -> CFunctor cat3 cat4
>   -> CFunctor (productCategory cat1 cat3) (productCategory cat2 cat4)
> productFunctor func1 func2 = MkCFunctor
>   (\a => (mapObj func1 (fst a), mapObj func2 (snd a)))
>   (\a, b, f => MkProductMorphism (mapMor func1 (fst a) (fst b) (pi1 f)) (mapMor func2 (snd a) (snd b) (pi2 f)))
>   (\a => cong2 {f = MkProductMorphism} (preserveId func1 (fst a)) (preserveId func2 (snd a)))
>   (\a, b, c, f, g => cong2 {f = MkProductMorphism} (preserveCompose func1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>                                                    (preserveCompose func2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g)))
