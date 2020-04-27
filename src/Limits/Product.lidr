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

> module Limits.Product
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Product.ProductCategory
> import public CoLimits.CoProduct
> import public Dual.DualCategory
> 
> %access public export
> %default total
> 
> Product : (cat : Category) -> (a : obj cat) -> (b : obj cat) -> Type
> Product cat a b = CoProduct (dualCategory cat) a b
> 
> productsAreIsomorphic :
>      (a, b : Product cat l r)
>   -> Isomorphic cat (carrier a) (carrier b)
> productsAreIsomorphic {cat} {l} {r} a b =
>   dualPreservesIsomorphic (coProductsAreIsomorphic (dualCategory cat) l r a b)
> 
> BinaryProduct : Category -> Type
> BinaryProduct cat = BinaryCoProduct (dualCategory cat)
> 
> binaryProductToFunctor :
>   BinaryProduct cat -> CFunctor (productCategory cat cat) cat
> binaryProductToFunctor {cat} p = MkCFunctor
>   mapObj
>   (\a, b => mapMor {a} {b})
>   preserveId
>   (\a, b, c => preserveCompose {a} {b} {c})
> where
>   mapObj : obj (productCategory cat cat) -> obj cat
>   mapObj (l, r) = carrier (p l r)
>   
>   mapMor : mor (productCategory cat cat) a b -> mor cat (mapObj a) (mapObj b)
>   mapMor {a=(al, ar)} {b=(bl, br)} (MkProductMorphism pi1 pi2) =
>     challenger
>       (exists (p bl br)
>               (carrier (p al ar))
>               (compose cat (carrier (p al ar)) al bl (inl (p al ar)) pi1)
>               (compose cat (carrier (p al ar)) ar br (inr (p al ar)) pi2))
> 
>   preserveId :
>        (a : obj (productCategory cat cat))
>     -> mapMor {a=a} {b=a} (identity (productCategory cat cat) a)
>        = identity cat (mapObj a)
>   preserveId (l, r) =
>     rewrite unique (p l r)
>               (carrier (p l r))
>               (inl (p l r))
>               (inr (p l r))
>               (idCommutingMorphism (dualCategory cat) l r (p l r)) in
>     rewrite rightIdentity cat (carrier (p l r)) l (inl (p l r)) in
>     rewrite rightIdentity cat (carrier (p l r)) r (inr (p l r)) in Refl
> 
>   preserveCompose :
>        (f : mor (productCategory cat cat) a b)
>     -> (g : mor (productCategory cat cat) b c)
>     -> mapMor {a=a} {b=c} (compose (productCategory cat cat) a b c f g)
>       = compose cat (mapObj a) (mapObj b) (mapObj c) (mapMor f) (mapMor g)
>   preserveCompose {a=(al, ar)} {b=(bl, br)} {c=(cl, cr)} (MkProductMorphism fpi1 fpi2) (MkProductMorphism gpi1 gpi2) =
>     rewrite associativity cat (carrier (p al ar)) al bl cl (inl (p al ar)) fpi1 gpi1 in
>     rewrite associativity cat (carrier (p al ar)) ar br cr (inr (p al ar)) fpi2 gpi2 in
>     rewrite unique (p cl cr)
>               (carrier (p al ar))
>               (compose cat (carrier (p al ar)) bl cl
>                            (compose cat (carrier (p al ar)) al bl
>                              (inl (p al ar)) fpi1)
>                            gpi1)
>               (compose cat (carrier (p al ar)) br cr
>                            (compose cat (carrier (p al ar)) ar br
>                              (inr (p al ar)) fpi2)
>                            gpi2)
>               (MkCommutingMorphism
>                 (compose cat (carrier (p al ar)) (carrier (p bl br)) (carrier (p cl cr))
> 						      (challenger (exists (p bl br)
> 																(carrier (p al ar))
> 																(compose cat (carrier (p al ar)) al bl (inl (p al ar)) fpi1)
> 																(compose cat (carrier (p al ar)) ar br (inr (p al ar)) fpi2)))
> 						      (challenger (exists (p cl cr)
> 																(carrier (p bl br))
> 																(compose cat (carrier (p bl br)) bl cl (inl (p bl br)) gpi1)
> 																(compose cat (carrier (p bl br)) br cr (inr (p bl br)) gpi2))))
>                 (believe_me ())
>                 (believe_me ())) in
>     Refl
