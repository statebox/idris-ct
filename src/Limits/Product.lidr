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
> import Basic.NaturalTransformation
> import Basic.NaturalIsomorphism
> import Product.ProductCategory
> import Limits.TerminalObject
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
>
> catHasTerminalObj : Category -> Type
> catHasTerminalObj = TerminalObject
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
> parameters (cat : Category, products : catHasProducts cat, terminal : catHasTerminalObj cat)
>   rightUnitorComponent : (a : obj cat) -> mor cat (carrier $ products a (carrier terminal)) a
>   rightUnitorComponent a = Product.pi1 $ products a (carrier terminal)
>
>   rightUnitorComm :
>        (a, b : obj cat)
>     -> (f : mor cat a b)
>     -> compose cat _ _ _ (rightUnitorComponent a) f
>      = compose cat _ _ _ (mapMor (bifunctorLeft cat (productFunctor cat products) (carrier terminal)) a b f)
>                          (rightUnitorComponent b)
>   rightUnitorComm a b f =
>     rewrite
>       rightIdentity cat (carrier (products a (carrier terminal)))
>                         (carrier terminal)
>                         (pi2 (products a (carrier terminal)))
>     in
>       sym $ commutativityLeft (exists (products b (carrier terminal))
>                               (carrier (products a (carrier terminal)))
>                               (compose cat (carrier (products a (carrier terminal)))
>                                            a b
>                                            (pi1 (products a (carrier terminal)))
>                                            f)
>                               (pi2 (products a (carrier terminal))))
>
>   rightUnitorNatTrans : NaturalTransformation cat cat
>                                               (bifunctorLeft cat (productFunctor cat products) (carrier terminal))
>                                               (idFunctor cat)
>   rightUnitorNatTrans = MkNaturalTransformation rightUnitorComponent rightUnitorComm
>
>   rightUnitorInverse : (a : obj cat) -> mor cat a (carrier $ products a (carrier terminal))
>   rightUnitorInverse a = challenger $ Product.exists (products a (carrier terminal))
>                                                      a
>                                                      (identity cat a)
>                                                      (exists terminal a)
>
>   commutativeIdentity :
>        (a, b : obj cat)
>     -> let pab = products a b in
>        CommutingMorphism cat (carrier pab) a b (carrier pab) (pi1 pab) (pi2 pab) (pi1 pab) (pi2 pab)
>   commutativeIdentity a b =
>     MkCommutingMorphism (identity cat $ carrier $ products a b)
>                         (leftIdentity cat (carrier $ products a b) a (pi1 $ products a b))
>                         (leftIdentity cat (carrier $ products a b) b (pi2 $ products a b))
>
>   productPi12Identity :
>        (a, b : obj cat)
>     -> let pab = products a b in
>        challenger $ Product.exists pab (carrier pab) (pi1 pab) (pi2 pab) = identity cat (carrier pab)
>   productPi12Identity a b = sym $ unique (products a b)
>                                          (carrier $ products a b)
>                                          (pi1 $ products a b)
>                                          (pi2 $ products a b)
>                                          (commutativeIdentity a b)
>
>   potentialIdentity :
>        (a : obj cat)
>     -> mor cat (carrier $ products a (carrier terminal)) (carrier $ products a (carrier terminal))
>   potentialIdentity a = compose cat
>               (carrier (products a (carrier terminal)))
>               a
>               (carrier (products a (carrier terminal)))
>               (pi1 (products a (carrier terminal)))
>               (challenger (exists (products a (carrier terminal)) a (identity cat a) (exists terminal a)))
>
>   potentialIdentityCommutingMorphism :
>        (a : obj cat)
>     -> let pa1 = products a (carrier terminal) in
>        CommutingMorphism cat (carrier pa1)
>                              a
>                              (carrier terminal)
>                              (carrier pa1)
>                              (pi1 pa1) (pi2 pa1)
>                              (compose cat _ _ _ (potentialIdentity a) (pi1 pa1))
>                              (compose cat _ _ _ (potentialIdentity a) (pi2 pa1))
>   potentialIdentityCommutingMorphism a = ?wat1
>
>   rightUnitorIsomorphism : (a : obj cat) -> Isomorphism cat _ _ (rightUnitorComponent a)
>   rightUnitorIsomorphism a = MkIsomorphism (rightUnitorInverse a)
>     ?wat0
>     (commutativityLeft $ Product.exists (products a (carrier terminal)) a (identity cat a) (exists terminal a))
>
>   rightUnitorNatIso : NaturalIsomorphism cat cat (bifunctorLeft cat (productFunctor cat products) (carrier terminal))
>                                                  (idFunctor cat)
>   rightUnitorNatIso = MkNaturalIsomorphism rightUnitorNatTrans rightUnitorIsomorphism

rightUnitorInverse a ;
pi1 ; <id_A, unique> = id_(A x (carrier terminal))

A x 1 - pi1 -> A
A x 1 - pi2 -> 1

<pi1, pi2> = id_(A x 1)

A x 1 - unique -> 1
==> unique = pi2



A x 1 -- pi1 --> A -- <id_A, unique> --> A x 1
pi1;<id_A, unique>;pi2 = pi1 ; id_A = pi1
pi1;<id_A, unique>;pi2 = pi1;unique = unique = pi2


A x 1 -- pi2 --> 1
  |              ^
  |              |
 pi1            pi2
  |              |
 \ /             |
  A <-- pi1 -- A x 1



exists a -> (id_a:a->a) -> (unique: a -> 1)
rightUnitorComponent: A x 1 -- pi1 -> A
inverse: A --> A x (carrier terminal)
A -- inverse := <id_A, unique> --> A x carrier terminal -- pi1 --> A



A -- unique --> carrier terminal
A -- id --> A


A x 1 -- pi1 --> A
    |                     |
    |                     |
  fxid1                f
    |                     |
   \ /                   \ /
B x 1 -- pi1 --> B




pi2, !


f: A --> B

A x 1 -- f x id1 -> B x 1


<pi1;f, pi2;id1> = <pi1;f,pi2;>

<pi1;f,pi2;> ; pi1 = pi1;f
