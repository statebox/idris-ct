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

> module Product.ProductCategory
>
> import Basic.Category
> import Basic.Functor
> import Utils
>
> %access public export
> %default total
>
> record ProductMorphism
>   (cat1 : Category)
>   (cat2 : Category)
>   (a : (obj cat1, obj cat2))
>   (b : (obj cat1, obj cat2))
>   where
>     constructor MkProductMorphism
>     pi1 : mor cat1 (fst a) (fst b)
>     pi2 : mor cat2 (snd a) (snd b)
>
> productIdentity :
>      (a : (obj cat1, obj cat2))
>   -> ProductMorphism cat1 cat2 a a
> productIdentity {cat1} {cat2} a = MkProductMorphism (identity cat1 (fst a)) (identity cat2 (snd a))
>
> productCompose :
>      (a, b, c : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> (g : ProductMorphism cat1 cat2 b c)
>   -> ProductMorphism cat1 cat2 a c
> productCompose {cat1} {cat2} a b c f g = MkProductMorphism
>   (compose cat1 (fst a) (fst b) (fst c) (pi1 f) (pi1 g))
>   (compose cat2 (snd a) (snd b) (snd c) (pi2 f) (pi2 g))
>
> productLeftIdentity :
>      (a, b : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> productCompose a a b (productIdentity a) f = f
> productLeftIdentity {cat1} {cat2} a b (MkProductMorphism f1 f2)
>   = cong2 {f = MkProductMorphism} (leftIdentity cat1 (fst a) (fst b) f1) (leftIdentity cat2 (snd a) (snd b) f2)
>
> productRightIdentity :
>      (a, b : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> productCompose a b b f (productIdentity b) = f
> productRightIdentity {cat1} {cat2} a b (MkProductMorphism f1 f2)
>   = cong2 {f = MkProductMorphism} (rightIdentity cat1 (fst a) (fst b) f1) (rightIdentity cat2 (snd a) (snd b) f2)
>
> productAssociativity :
>      (a, b, c, d : (obj cat1, obj cat2))
>   -> (f : ProductMorphism cat1 cat2 a b)
>   -> (g : ProductMorphism cat1 cat2 b c)
>   -> (h : ProductMorphism cat1 cat2 c d)
>   -> productCompose a b d f (productCompose b c d g h) = productCompose a c d (productCompose a b c f g) h
> productAssociativity {cat1} {cat2} a b c d f g h = cong2 {f = MkProductMorphism}
>   (associativity cat1 (fst a) (fst b) (fst c) (fst d) (pi1 f) (pi1 g) (pi1 h))
>   (associativity cat2 (snd a) (snd b) (snd c) (snd d) (pi2 f) (pi2 g) (pi2 h))
>
> productCategory : (cat1, cat2 : Category) -> Category
> productCategory cat1 cat2 = MkCategory
>   (obj cat1, obj cat2)
>   (ProductMorphism cat1 cat2)
>   (productIdentity {cat1} {cat2})
>   (productCompose {cat1} {cat2})
>   (productLeftIdentity {cat1} {cat2})
>   (productRightIdentity {cat1} {cat2})
>   (productAssociativity {cat1} {cat2})
>
> productAssociator :
>      (cat1, cat2, cat3 : Category)
>   -> CFunctor (productCategory cat1 (productCategory cat2 cat3)) (productCategory (productCategory cat1 cat2) cat3)
> productAssociator cat1 cat2 cat3 = MkCFunctor
>   (\abc => ((fst abc, fst (snd abc)), (snd (snd abc))))
>   (\abc1, abc2, f => MkProductMorphism (MkProductMorphism (pi1 f) (pi1 (pi2 f))) (pi2 (pi2 f)))
>   (\abc => Refl)
>   (\abc1, abc2, abc3, f, g => Refl)
