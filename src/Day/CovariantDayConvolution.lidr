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

> module Day.CovariantDayConvolution
>
> import Basic.Category
> import Basic.Functor
> import Idris.TypesAsCategoryExtensional
> import MonoidalCategory.MonoidalCategory
> import Product.ProductCategory
> import Utils
>
> %access public export
> %default total
>
> Day :
>      {moncat : MonoidalCategory}
>   -> (fun1, fun2 : CFunctor (cat moncat) TypesAsCategoryExtensional.typesAsCategoryExtensional)
>   -> CFunctor (cat moncat) TypesAsCategoryExtensional.typesAsCategoryExtensional
> Day {moncat} fun1 fun2 = MkCFunctor
>   (\a => (  x : obj (cat moncat)
>          ** (y : obj (cat moncat)
>          ** (mapObj fun1 x, mapObj fun2 y, mor (cat moncat) (mapObj (tensor moncat) (x, y)) a))))
>   (\a, b, f => MkExtensionalTypeMorphism
>                  (\k => (  (fst k)
>                         ** (fst $ snd k)
>                         ** ( fst (DPair.snd $ DPair.snd k)
>                            , fst $ snd (DPair.snd $ DPair.snd k)
>                            , compose (cat moncat)
>                                      (mapObj (tensor moncat) (fst k, fst $ snd k))
>                                      a
>                                      b
>                                      (snd $ snd (DPair.snd $ DPair.snd k)) f))))
>   (\a => funExt (\x => dPairEq Refl (dPairEq Refl (pairEq Refl (pairEq Refl
>            (rightIdentity (cat moncat)
>                           (mapObj (tensor moncat) (fst x, fst (snd x)))
>                           a
>                           (snd (snd (snd (snd x))))))))))
>   (\a, b, c, f, g => funExt (\x => dPairEq Refl (dPairEq Refl (pairEq Refl (pairEq Refl
>                        (associativity (cat moncat)
>                                       (mapObj (tensor moncat) (fst x, fst (snd x)))
>                                       a
>                                       b
>                                       c
>                                       (snd (snd (snd (snd x))))
>                                       f
>                                       g))))))
