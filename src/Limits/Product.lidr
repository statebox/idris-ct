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
>   -> (product : catHasProducts cat)
>   -> CFunctor (productCategory cat cat) cat
> productFunctor cat product = MkCFunctor mapObj mapMor idLaw compLaw
>   where
>     mapObj : (obj cat, obj cat) -> obj cat
>     mapObj (a,b) = carrier $ product a b
>     mapMor :
>          (a, b : obj (productCategory cat cat))
>       -> mor (productCategory cat cat) a b
>       -> mor cat (mapObj a) (mapObj b)
>     mapMor (a1,b1) (a2,b2) (MkProductMorphism f g) =
>       productMorphism cat a1 a2 b1 b2 f g (product a1 b1) (product a2 b2)
>     identityCommutingMorphism :
>          (a,b : obj cat)
>       -> CommutingMorphism cat
>                            (carrier (product a b)) a b (carrier (product a b))
>                            (pi1 (product a b)) (pi2 (product a b))
>                            (compose cat (carrier (product a b)) a a (pi1 (product a b)) (identity cat a))
>                            (compose cat (carrier (product a b)) b b (pi2 (product a b)) (identity cat b))
>     identityCommutingMorphism a b =
>       MkCommutingMorphism (identity cat (carrier (product a b)))
>                           (rewrite leftIdentity cat (carrier (product a b)) a (pi1 (product a b)) in
>                             sym $ rightIdentity cat (carrier (product a b)) a (pi1 (product a b)))
>                           (rewrite leftIdentity cat (carrier (product a b)) b (pi2 (product a b)) in
>                             sym $ rightIdentity cat (carrier (product a b)) b (pi2 (product a b)))
>     idLaw :
>          (a : obj (productCategory cat cat))
>       -> mapMor a a (identity (productCategory cat cat) a) = identity cat (mapObj a)
>     idLaw (a,b) = sym $ unique (product a b)
>                                (carrier (product a b))
>                                (compose cat (carrier (product a b)) a a (pi1 (product a b)) (identity cat a))
>                                (compose cat (carrier (product a b)) b b (pi2 (product a b)) (identity cat b))
>                                (identityCommutingMorphism a b)
>     compComMor : (a1,a2,b1,b2,c1,c2 : obj cat) 
>               -> (f1 : mor cat a1 b1) -> (f2 : mor cat a2 b2) 
>               -> (g1 : mor cat b1 c1) -> (g2 : mor cat b2 c2)
>               -> CommutingMorphism cat (carrier (product a1 a2)) c1 c2 
>                                    (carrier (product c1 c2)) (pi1 (product c1 c2)) (pi2 (product c1 c2)) 
>                                    (compose cat (carrier (product a1 a2)) a1 c1 (pi1 (product a1 a2)) (compose cat a1 b1 c1 f1 g1))
>                                    (compose cat (carrier (product a1 a2)) a2 c2 (pi2 (product a1 a2)) (compose cat a2 b2 c2 f2 g2))
>     compComMor a1 a2 b1 b2 c1 c2 f1 f2 g1 g2 = 
>       let 
>         pa = product a1 a2
>         pb = product b1 b2
>         pc = product c1 c2
>         cmab = exists pb (carrier pa) (compose cat (carrier pa) a1 b1 (pi1 pa) f1)
>                                       (compose cat (carrier pa) a2 b2 (pi2 pa) f2)
>         cmbc = exists pc (carrier pb) (compose cat (carrier pb) b1 c1 (pi1 pb) g1)
>                                       (compose cat (carrier pb) b2 c2 (pi2 pb) g2)
>        in
>       MkCommutingMorphism (compose cat (carrier pa) (carrier pb) (carrier pc) (challenger cmab) (challenger cmbc)) 
>                           (rewrite sym $ associativity cat (carrier pa) (carrier pb) (carrier pc) c1
>                                                            (challenger cmab) (challenger cmbc) (pi1 pc) in
>                            rewrite commutativityLeft cmbc in 
>                            rewrite associativity cat (carrier pa) (carrier pb) b1 c1
>                                                      (challenger cmab) (pi1 pb) g1 in
>                            rewrite commutativityLeft cmab in 
>                            sym $ associativity cat (carrier pa) a1 b1 c1 
>                                                    (pi1 pa) f1 g1) 
>                           (rewrite sym $ associativity cat (carrier pa) (carrier pb) (carrier pc) c2
>                                                            (challenger cmab) (challenger cmbc) (pi2 pc) in
>                            rewrite commutativityRight cmbc in 
>                            rewrite associativity cat (carrier pa) (carrier pb) b2 c2
>                                                      (challenger cmab) (pi2 pb) g2 in
>                            rewrite commutativityRight cmab in 
>                            sym $ associativity cat (carrier pa) a2 b2 c2 
>                                                    (pi2 pa) f2 g2) 
>     compLaw : 
>          (a,b,c : (obj cat, obj cat)) ->
>          (f : ProductMorphism cat cat a b) ->
>          (g : ProductMorphism cat cat b c) ->
>          mapMor a c (productCompose a b c f g) =
>          compose cat (mapObj a) (mapObj b) (mapObj c) (mapMor a b f) (mapMor b c g)
>     compLaw (a1,a2) (b1,b2) (c1,c2) (MkProductMorphism f1 f2) (MkProductMorphism g1 g2) = 
>       sym $ unique (product c1 c2) 
>                    (carrier (product a1 a2)) 
>                    (compose cat (carrier (product a1 a2)) a1 c1 (pi1 (product a1 a2)) (compose cat a1 b1 c1 f1 g1))
>                    (compose cat (carrier (product a1 a2)) a2 c2 (pi2 (product a1 a2)) (compose cat a2 b2 c2 f2 g2))
>                    (compComMor a1 a2 b1 b2 c1 c2 f1 f2 g1 g2)
>
> bifunctorLeft :
>      (cat : Category)
>   -> (fun : CFunctor (productCategory cat cat) cat)
>   -> (b : obj cat)
>   -> CFunctor cat cat
> bifunctorLeft cat (MkCFunctor mapObj mapMor pId pComp) b = MkCFunctor mapObj' mapMor' pId' pComp'
>   where
>     mapObj' : obj cat -> obj cat
>     mapObj' x = mapObj (x, b)
>
>     mapMor' : (x, y : obj cat) -> mor cat x y -> mor cat (mapObj' x) (mapObj' y)
>     mapMor' x y mor = mapMor (x, b) (y, b) (MkProductMorphism mor (identity cat b))
>
>     pId' :
>          (x : obj cat)
>       -> mapMor (x, b) (x, b) (MkProductMorphism (identity cat x) (identity cat b))
>        = identity cat (mapObj (x, b))
>     pId' x = pId (x, b)
>
>     pComp' :
>          (x, y, z : obj cat)
>       -> (f : mor cat x y)
>       -> (g : mor cat y z)
>       -> mapMor (x, b) (z, b) (MkProductMorphism (compose cat x y z f g) (identity cat b))
>        = compose cat (mapObj (x, b))
>                      (mapObj (y, b))
>                      (mapObj (z, b))
>                      (mapMor (x, b) (y, b) (MkProductMorphism f (identity cat b)))
>                      (mapMor (y, b) (z, b) (MkProductMorphism g (identity cat b)))
>     pComp' x y z f g =
>       replace {P=\q => mapMor (x, b) (z, b) (MkProductMorphism (compose cat x y z f g) q)
>                      = compose cat (mapObj (x, b))
>                                    (mapObj (y, b))
>                                    (mapObj (z, b))
>                                    (mapMor (x, b) (y, b) (MkProductMorphism f (identity cat b)))
>                                    (mapMor (y, b) (z, b) (MkProductMorphism g (identity cat b)))}
>               (leftIdentity cat b b (identity cat b))
>               (pComp (x,b) (y,b) (z,b) (MkProductMorphism f (identity cat b)) (MkProductMorphism g (identity cat b)))
>
> bifunctorRight :
>      (cat : Category)
>   -> (fun : CFunctor (productCategory cat cat) cat)
>   -> (a : obj cat)
>   -> CFunctor cat cat
> bifunctorRight cat (MkCFunctor mapObj mapMor pId pComp) a = MkCFunctor mapObj' mapMor' pId' pComp'
>   where
>     mapObj' : obj cat -> obj cat
>     mapObj' x = mapObj (a, x)
>
>     mapMor' : (x, y : obj cat) -> mor cat x y -> mor cat (mapObj' x) (mapObj' y)
>     mapMor' x y mor = mapMor (a, x) (a, y) (MkProductMorphism (identity cat a) mor)
>
>     pId' :
>          (x : obj cat)
>       -> mapMor (a, x) (a, x) (MkProductMorphism (identity cat a) (identity cat x))
>        = identity cat (mapObj (a, x))
>     pId' x = pId (a, x)
>
>     pComp' :
>          (x, y, z : obj cat)
>       -> (f : mor cat x y)
>       -> (g : mor cat y z)
>       -> mapMor (a, x) (a, z) (MkProductMorphism (identity cat a) (compose cat x y z f g))
>        = compose cat (mapObj (a, x))
>                      (mapObj (a, y))
>                      (mapObj (a, z))
>                      (mapMor (a, x) (a, y) (MkProductMorphism (identity cat a) f))
>                      (mapMor (a, y) (a, z) (MkProductMorphism (identity cat a) g))
>     pComp' x y z f g =
>       replace {P=\q => mapMor (a, x) (a, z) (MkProductMorphism q (compose cat x y z f g))
>                      = compose cat (mapObj (a, x))
>                                    (mapObj (a, y))
>                                    (mapObj (a, z))
>                                    (mapMor (a, x) (a, y) (MkProductMorphism (identity cat a) f))
>                                    (mapMor (a, y) (a, z) (MkProductMorphism (identity cat a) g))}
>               (rightIdentity cat a a (identity cat a))
>               (pComp (a,x) (a,y) (a,z) (MkProductMorphism (identity cat a) f) (MkProductMorphism (identity cat a) g))
>