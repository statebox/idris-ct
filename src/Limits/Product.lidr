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
> import Product.ProductCategory
>
> %access public export
> %default total
> %auto_implicits off
>
> record CommutingMorphism
>   (cat : Category)
>   (x : obj cat) (a : obj cat) (b : obj cat) (carrier : obj cat)
>   (pi1 : mor cat carrier a) (pi2 : mor cat carrier b)
>   (f : mor cat x a) (g : mor cat x b)
> where
>   constructor MkCommutingMorphism
>   challenger         : mor cat x carrier
>   commutativityLeft  : compose cat x carrier a challenger pi1 = f
>   commutativityRight : compose cat x carrier b challenger pi2 = g
>
> record Product (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkProduct
>   carrier : obj cat
>   pi1 : mor cat carrier a
>   pi2 : mor cat carrier b
>   exists :
>        (x : obj cat)
>     -> (f : mor cat x a)
>     -> (g : mor cat x b)
>     -> CommutingMorphism cat x a b carrier pi1 pi2 f g
>   unique :
>        (x : obj cat)
>     -> (f : mor cat x a)
>     -> (g : mor cat x b)
>     -> (h : CommutingMorphism cat x a b carrier pi1 pi2 f g)
>     -> challenger h = challenger (exists x f g)
>
> productMorphism :
>      (cat : Category)
>   -> (a1, a2, b1, b2 : obj cat)
>   -> (f : mor cat a1 a2)
>   -> (g : mor cat b1 b2)
>   -> (pr1 : Product cat a1 b1)
>   -> (pr2 : Product cat a2 b2)
>   -> mor cat (carrier pr1) (carrier pr2)
> productMorphism cat a1 a2 b1 b2 f g pr1 pr2 =
>   challenger $ exists pr2 (carrier pr1) (compose cat _ _ _ (pi1 pr1) f) (compose cat _ _ _ (pi2 pr1) g)
>
> catHasProducts : Category -> Type
> catHasProducts cat = (a, b : obj cat) -> Product cat a b
>
> productFunctor :
>      (cat : Category)
>   -> (productObj : catHasProducts cat)
>   -> CFunctor (productCategory cat cat) cat
> productFunctor cat productObj = MkCFunctor mapObj mapMor idLaw ?compLaw
>   where
>     mapObj : (obj cat, obj cat) -> obj cat
>     mapObj (a,b) = carrier $ productObj a b
>     mapMor :
>          (a, b : obj (productCategory cat cat))
>       -> mor (productCategory cat cat) a b
>       -> mor cat (mapObj a) (mapObj b)
>     mapMor (a1,b1) (a2,b2) (MkProductMorphism f g) =
>       productMorphism cat a1 a2 b1 b2 f g (productObj a1 b1) (productObj a2 b2)
>     identityCommutingMorphism :
>          (a,b : obj cat)
>       -> CommutingMorphism cat
>                            (carrier (productObj a b)) a b (carrier (productObj a b))
>                            (pi1 (productObj a b)) (pi2 (productObj a b))
>                            (compose cat (carrier (productObj a b)) a a (pi1 (productObj a b)) (identity cat a))
>                            (compose cat (carrier (productObj a b)) b b (pi2 (productObj a b)) (identity cat b))
>     identityCommutingMorphism a b =
>       MkCommutingMorphism (identity cat (carrier (productObj a b)))
>                           (rewrite leftIdentity cat (carrier (productObj a b)) a (pi1 (productObj a b)) in
>                             sym $ rightIdentity cat (carrier (productObj a b)) a (pi1 (productObj a b)))
>                           (rewrite leftIdentity cat (carrier (productObj a b)) b (pi2 (productObj a b)) in
>                             sym $ rightIdentity cat (carrier (productObj a b)) b (pi2 (productObj a b)))
>     idLaw :
>          (a : obj (productCategory cat cat))
>       -> mapMor a a (identity (productCategory cat cat) a) = identity cat (mapObj a)
>     idLaw (a,b) = sym $ unique (productObj a b)
>                                (carrier (productObj a b))
>                                (compose cat (carrier (productObj a b)) a a (pi1 (productObj a b)) (identity cat a))
>                                (compose cat (carrier (productObj a b)) b b (pi2 (productObj a b)) (identity cat b))
>                                (identityCommutingMorphism a b)
