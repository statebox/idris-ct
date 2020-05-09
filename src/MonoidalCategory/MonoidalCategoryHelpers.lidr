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

> module MonoidalCategory.MonoidalCategoryHelpers
> 
> import Basic.Category
> import Basic.Functor
> import Basic.NaturalIsomorphism
> import Basic.NaturalTransformation
> import Data.Vect
> import Product.ProductCategory
> import Product.ProductFunctor
> 
> %access public export
> %default total
> 
> leftTensor3 :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> CFunctor (productCategory [cat, cat, cat]) cat
> leftTensor3 cat tensor = MkCFunctor
>   mObj
>   mMor
>   pId
>   pCompose
> where
>   mObj : obj (productCategory [cat, cat, cat]) -> obj cat
>   mObj (a, b, c, ()) = mapObj tensor ((mapObj tensor (a, b, ())), c, ())
> 
>   mMor :
>        (a, b : obj (productCategory [cat, cat, cat]))
>     -> mor (productCategory [cat, cat, cat]) a b -> mor cat (mObj a) (mObj b)
>   mMor (a1, a2, a3, ()) (b1, b2, b3, ()) (f1, f2, f3, ()) =
>     mapMor tensor
>       (mapObj tensor (a1, a2, ()), a3, ())
>       (mapObj tensor (b1, b2, ()), b3, ())
>       (mapMor tensor
>          (a1, a2, ())
>          (b1, b2, ())
>          (f1, f2, ())
>       , f3
>       , ())
> 
>   pId : (a : obj (productCategory [cat, cat, cat]))
>     -> mMor a a (identity (productCategory [cat, cat, cat]) a) = identity cat (mObj a)
>   pId (a, b, c, ()) = rewrite preserveId tensor (a, b, ()) in preserveId tensor (mapObj tensor (a, b, ()), c, ())
> 
>   pCompose : (a, b, c : obj (productCategory [cat, cat, cat]))
>     -> (f : mor (productCategory [cat, cat, cat]) a b)
>     -> (g : mor (productCategory [cat, cat, cat]) b c)
>     -> mMor a c (compose (productCategory [cat, cat, cat]) a b c f g)
>      = compose cat (mObj a) (mObj b) (mObj c) (mMor a b f) (mMor b c g)
>   pCompose (a1, a2, a3, ()) (b1, b2, b3, ()) (c1, c2, c3, ())
>            (f1, f2, f3, ()) (g1, g2, g3, ()) =
>     rewrite preserveCompose tensor (a1, a2, ()) (b1, b2, ()) (c1, c2, ())
>                                    (f1, f2, ()) (g1, g2, ()) in
>     preserveCompose tensor
>       ((mapObj tensor (a1, a2, ())), a3, ())
>       ((mapObj tensor (b1, b2, ())), b3, ())
>       ((mapObj tensor (c1, c2, ())), c3, ())
>       ((mapMor tensor (a1, a2, ()) (b1, b2, ())
>                       (f1, f2, ())), f3, ())
>       ((mapMor tensor (b1, b2, ()) (c1, c2, ())
>                       (g1, g2, ())), g3, ())
> 
> rightTensor3 :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> CFunctor (productCategory [cat, cat, cat]) cat
> rightTensor3 cat tensor = MkCFunctor
>   mObj
>   mMor
>   pId
>   pCompose
> where
>   mObj : obj (productCategory [cat, cat, cat]) -> obj cat
>   mObj (a, b, c, ()) = mapObj tensor (a, (mapObj tensor (b, c, ())), ())
> 
>   mMor :
>        (a, b : obj (productCategory [cat, cat, cat]))
>     -> mor (productCategory [cat, cat, cat]) a b -> mor cat (mObj a) (mObj b)
>   mMor (a1, a2, a3, ()) (b1, b2, b3, ()) (f1, f2, f3, ()) =
>     mapMor tensor
>       (a1, mapObj tensor (a2, a3, ()), ())
>       (b1, mapObj tensor (b2, b3, ()), ())
>       (f1
>        , mapMor tensor
>            (a2, a3, ())
>            (b2, b3, ())
>            (f2, f3, ())
>        , ())
> 
>   pId : (a : obj (productCategory [cat, cat, cat]))
>     -> mMor a a (identity (productCategory [cat, cat, cat]) a) = identity cat (mObj a)
>   pId (a, b, c, ()) = rewrite preserveId tensor (b, c, ()) in preserveId tensor (a, mapObj tensor (b, c, ()), ())
> 
>   pCompose : (a, b, c : obj (productCategory [cat, cat, cat]))
>     -> (f : mor (productCategory [cat, cat, cat]) a b)
>     -> (g : mor (productCategory [cat, cat, cat]) b c)
>     -> mMor a c (compose (productCategory [cat, cat, cat]) a b c f g)
>      = compose cat (mObj a) (mObj b) (mObj c) (mMor a b f) (mMor b c g)
>   pCompose (a1, a2, a3, ()) (b1, b2, b3, ()) (c1, c2, c3, ())
>            (f1, f2, f3, ()) (g1, g2, g3, ()) =
>     rewrite preserveCompose tensor (a2, a3, ()) (b2, b3, ()) (c2, c3, ())
>                                    (f2, f3, ()) (g2, g3, ()) in
>     preserveCompose tensor
>       (a1, (mapObj tensor (a2, a3, ())), ())
>       (b1, (mapObj tensor (b2, b3, ())), ())
>       (c1, (mapObj tensor (c2, c3, ())), ())
>       (f1, (mapMor tensor (a2, a3, ()) (b2, b3, ())
>                           (f2, f3, ())), ())
>       (g1, (mapMor tensor (b2, b3, ()) (c2, c3, ())
>                           (g2, g3, ())), ())
> 
> Associator :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> Type
> Associator cat tensor = NaturalIsomorphism (productCategory [cat, cat, cat])
>                                            cat
>                                            (leftTensor3  cat tensor)
>                                            (rightTensor3 cat tensor)
> leftIdTensor :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> (unit : obj cat)
>   -> CFunctor cat cat
> leftIdTensor cat tensor unit = MkCFunctor
>   mObj
>   mMor
>   pId
>   pCompose
> where
>   mObj : obj cat -> obj cat
>   mObj a = mapObj tensor (unit, a, ())
> 
>   mMor : (a, b : obj cat) -> mor cat a b -> mor cat (mObj a) (mObj b)
>   mMor a b f = mapMor tensor (unit, a, ()) (unit, b, ()) ((identity cat unit), f, ())
> 
>   pId : (a : obj cat) -> mMor a a (identity cat a) = identity cat (mObj a)
>   pId a = preserveId tensor (unit, a, ())
> 
>   pCompose : (a, b, c : obj cat) -> (f : mor cat a b) -> (g : mor cat b c) -> 
>       mMor a c (compose cat a b c f g) = compose cat (mObj a) (mObj b) (mObj c) (mMor a b f) (mMor b c g)
>   pCompose a b c f g = rewrite sym (preserveCompose tensor (unit, a, ()) (unit, b, ()) (unit, c, ()) 
>                          ((identity cat unit), f, ()) ((identity cat unit), g, ())) in rewrite leftIdentity cat (unit) (unit) (identity cat unit) in Refl
> 
> rightIdTensor :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> (unit : obj cat)
>   -> CFunctor cat cat
> rightIdTensor cat tensor unit = MkCFunctor
>   mObj
>   mMor
>   pId
>   pCompose
> where
>   mObj : obj cat -> obj cat
>   mObj a = mapObj tensor (a, unit, ())
> 
>   mMor : (a, b : obj cat) -> mor cat a b -> mor cat (mObj a) (mObj b)
>   mMor a b f = mapMor tensor (a, unit, ()) (b, unit, ()) (f, (identity cat unit), ())
> 
>   pId : (a : obj cat) -> mMor a a (identity cat a) = identity cat (mObj a)
>   pId a = preserveId tensor (a, unit, ())
> 
>   pCompose : (a, b, c : obj cat) -> (f : mor cat a b) -> (g : mor cat b c) -> 
>       mMor a c (compose cat a b c f g) = compose cat (mObj a) (mObj b) (mObj c) (mMor a b f) (mMor b c g)
>   pCompose a b c f g = rewrite sym (preserveCompose tensor (a, unit, ()) (b, unit, ()) (c, unit, ()) 
>                          (f, (identity cat unit), ()) (g, (identity cat unit), ())) in rewrite leftIdentity cat (unit) (unit) (identity cat unit) in Refl
> 
> MonoidalPentagon :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> (associator : Associator cat tensor)
>   -> (a, b, c, d : obj cat)
>   -> Type
> MonoidalPentagon cat tensor associator a b c d =
>   (compose cat
>            (mapObj tensor (mapObj tensor (mapObj tensor (a, b, ()), c, ()), d, ()))
>            (mapObj tensor (mapObj tensor (a, b, ()), mapObj tensor (c, d, ()), ()))
>            (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d, ()), ())), ()))
>            (component (natTrans associator) (mapObj tensor (a, b, ()), c, d, ()))
>            (component (natTrans associator) (a, b, mapObj tensor (c, d, ()), ())))
>            =
>   (compose cat
>            (mapObj tensor (mapObj tensor (mapObj tensor (a, b, ()), c, ()), d, ()))
>            (mapObj tensor (mapObj tensor (a, mapObj tensor (b, c, ()), ()), d, ()))
>            (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d, ()), ())), ()))
>            (mapMor tensor
>                    (mapObj tensor (mapObj tensor (a, b, ()), c, ()), d, ())
>                    (mapObj tensor (a, mapObj tensor (b, c, ()), ()), d, ())
>                    ((component (natTrans associator) (a, b, c, ())), (identity cat d), ()))
>            (compose cat
>                     (mapObj tensor (mapObj tensor (a, mapObj tensor (b, c, ()), ()), d, ()))
>                     (mapObj tensor (a, mapObj tensor (mapObj tensor (b, c, ()), d, ()), ()))
>                     (mapObj tensor (a, (mapObj tensor (b, mapObj tensor (c, d, ()), ())), ()))
>                     (component (natTrans associator) (a, mapObj tensor (b, c, ()), d, ()))
>                     (mapMor tensor
>                             (a, mapObj tensor (mapObj tensor (b, c, ()), d, ()), ())
>                             (a, (mapObj tensor (b, mapObj tensor (c, d, ()), ())), ())
>                             ((identity cat a), (component (natTrans associator) (b, c, d, ())), ()))))
> 
> MonoidalTriangle :
>      (cat : Category)
>   -> (tensor : CFunctor (productCategory [cat, cat]) cat)
>   -> (unit : obj cat)
>   -> (associator : Associator cat tensor)
>   -> (leftUnitor  : NaturalIsomorphism cat cat (leftIdTensor  cat tensor unit) (idFunctor cat))
>   -> (rightUnitor : NaturalIsomorphism cat cat (rightIdTensor cat tensor unit) (idFunctor cat))
>   -> (a, b : obj cat)
>   -> Type
> MonoidalTriangle cat tensor unit associator leftUnitor rightUnitor a b =
>   (mapMor tensor
>           (mapObj tensor (a, unit, ()), b, ())
>           (a, b, ())
>           ((component (natTrans rightUnitor) a), (identity cat b), ()))
>           =
>   (compose cat
>            (mapObj tensor (mapObj tensor (a, unit, ()), b, ()))
>            (mapObj tensor (a, mapObj tensor (unit, b, ()), ()))
>            (mapObj tensor (a, b, ()))
>            (component (natTrans associator) (a, unit, b, ()))
>            (mapMor tensor
>                    (a, mapObj tensor (unit, b, ()), ())
>                    (a, b, ())
>                    ((identity cat a), (component (natTrans leftUnitor) b), ())))
