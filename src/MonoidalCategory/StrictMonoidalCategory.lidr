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

> module MonoidalCategory.StrictMonoidalCategory
>
> import Basic.Category
> import Basic.Functor
> import Product.ProductCategory
>
> %access public export
> %default total
>
> record StrictMonoidalCategory where
>   constructor MkStrictMonoidalCategory
>   cat : Category
>   tensor : CFunctor (productCategory cat cat) cat
>   unit : obj cat
>   tensorIsLeftUnital  : (a : obj cat) -> (mapObj tensor) (unit, a) = a
>   tensorIsRightUnital : (a : obj cat) -> (mapObj tensor) (a, unit) = a
>   tensorIsAssociativeObj : (a, b, c : obj cat)
>                         -> mapObj tensor (a, mapObj tensor (b, c)) = mapObj tensor (mapObj tensor (a, b), c)
>   tensorIsAssociativeMor : (a, b, c, d, e, f : obj cat)
>                         -> (g : mor cat a b)
>                         -> (h : mor cat c d)
>                         -> (k : mor cat e f)
>                         -> mapMor tensor
>                                   (a, mapObj tensor (c,e))
>                                   (b, mapObj tensor (d,f))
>                                   (MkProductMorphism g (mapMor tensor (c,e) (d,f) (MkProductMorphism h k)))
>                          = mapMor tensor
>                                   (mapObj tensor (a,c), e)
>                                   (mapObj tensor (b,d), f)
>                                   (MkProductMorphism (mapMor tensor (a,c) (b,d) (MkProductMorphism g h)) k)
