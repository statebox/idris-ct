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

> module Higher.Bicategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Product.ProductCategory as PC
> import Product.ProductFunctor
>
> %access public export
> %default total
>
> horizontalIdPostcomposition : {cat1, cat2, cat3 : Category}
>                            -> (obj cat2)
>                            -> (hc : CFunctor (PC.productCategory cat1 cat2) cat3)
>                            -> CFunctor cat1 cat3
> horizontalIdPostcomposition {cat1} {cat2} identityMorphism hc = MkCFunctor
>   (\a => mapObj hc (a, identityMorphism))
>   (\a, b, f => mapMor hc
>                       (a, identityMorphism)
>                       (b, identityMorphism)
>                       (MkProductMorphism f (identity cat2 identityMorphism)))
>   (\a => preserveId hc (a, identityMorphism))
>   (\a, b, c, f, g => let pc = preserveCompose hc
>                                     (a, identityMorphism)
>                                     (b, identityMorphism)
>                                     (c, identityMorphism)
>                                     (MkProductMorphism f (identity cat2 identityMorphism))
>                                     (MkProductMorphism g (identity cat2 identityMorphism))
>                      in trans (cong {f=\x => mapMor hc
>                                              (a, identityMorphism)
>                                              (c, identityMorphism)
>                                              (MkProductMorphism (compose cat1 a b c f g) x)}
>                                     (sym $ leftIdentity cat2
>                                                         identityMorphism
>                                                         identityMorphism
>                                                         (identity cat2 identityMorphism)))
>                               pc)
>
> horizontalIdPrecomposition : {cat1, cat2, cat3 : Category}
>                           -> (obj cat1)
>                           -> (hc : CFunctor (PC.productCategory cat1 cat2) cat3)
>                           -> CFunctor cat2 cat3
> horizontalIdPrecomposition identityMorphism hc = horizontalIdPostcomposition
>   identityMorphism
>   (functorComposition _ _ _ flipFunctor hc)
>
> leftAssociator : {cat1, cat2, cat3, cat4, cat5 : Category}
>               -> CFunctor (PC.productCategory cat2 cat3) cat5
>               -> CFunctor (PC.productCategory cat1 cat5) cat4
>               -> CFunctor (PC.productCategory cat1 (PC.productCategory cat2 cat3)) cat4
> leftAssociator {cat1} {cat2} {cat3} {cat4} {cat5} f g = functorComposition
>   (PC.productCategory cat1 (PC.productCategory cat2 cat3))
>   (PC.productCategory cat1 cat5)
>   cat4
>   (productFunctor (idFunctor cat1) f)
>   g
>
> rightAssociator : {cat1, cat2, cat3, cat4, cat5 : Category}
>                -> CFunctor (PC.productCategory cat1 cat2) cat5
>                -> CFunctor (PC.productCategory cat5 cat3) cat4
>                -> CFunctor (PC.productCategory cat1 (PC.productCategory cat2 cat3)) cat4
> rightAssociator {cat1} {cat2} {cat3} {cat4} {cat5} f g = functorComposition
>   (PC.productCategory cat1 (PC.productCategory cat2 cat3))
>   (PC.productCategory (PC.productCategory cat1 cat2) cat3)
>   cat4
>   (PC.productAssociator cat1 cat2 cat3)
>   (functorComposition (PC.productCategory (PC.productCategory cat1 cat2) cat3)
>                       (PC.productCategory cat5 cat3)
>                       cat4
>                       (productFunctor f (idFunctor cat3))
>                       g)
>
> record Bicategory where
>   constructor MkBicategory
>   cell0                 : Type
>   cell1                 : cell0 -> cell0 -> Category
>   identity1cell         : (x : cell0) -> obj (cell1 x x)
>   horizontalComposition : {x, y, z : cell0}
>                        -> CFunctor (PC.productCategory (cell1 x y) (cell1 y z)) (cell1 x z)
>   leftUnitor            : {x, y : cell0}
>                        -> NaturalIsomorphism (cell1 x y)
>                                              (cell1 x y)
>                                              (horizontalIdPrecomposition (identity1cell x) horizontalComposition)
>                                              (idFunctor (cell1 x y))
>   rightUnitor           : {x, y : cell0}
>                        -> NaturalIsomorphism (cell1 x y)
>                                              (cell1 x y)
>                                              (horizontalIdPostcomposition (identity1cell y) horizontalComposition)
>                                              (idFunctor (cell1 x y))
>   -- associator            : {w, x, y, z : cell0}
>   --                      -> NaturalIsomorphism (PC.productCategory (cell1 w x)
>   --                                                                (PC.productCategory (cell1 x y) (cell1 y z)))
>   --                                            (cell1 w z)
>   --                                            (leftAssociator horizontalComposition horizontalComposition {cat1 = cell1 w x} {cat2 = cell1 x y} {cat3 = cell1 y z} {cat4 = cell1 w z})
>   --                                            (rightAssociator horizontalComposition horizontalComposition {cat1 = cell1 w x} {cat2 = cell1 x y} {cat3 = cell1 y z} {cat4 = cell1 w z})
