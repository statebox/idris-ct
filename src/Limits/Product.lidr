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

 rhoUnitor 

> catHasTerminalObj : Category -> Type
> catHasTerminalObj = TerminalObject
>
> bifunctorLeft : (cat : Category) -> (fun : CFunctor (productCategory cat cat) cat) -> (b : obj cat) -> CFunctor cat cat
> bifunctorLeft cat fun@(MkCFunctor mapObj mapMor pId pComp) b = MkCFunctor mapObj' mapMor' pId' pComp'
>   where 
>     mapObj' : obj cat -> obj cat
>     mapObj' x = mapObj (x, b)
>     mapMor' : (x, y : obj cat) -> mor cat x y -> mor cat (mapObj' x) (mapObj' y)
>     mapMor' x y mor = mapMor (x, b) (y, b) (MkProductMorphism mor (identity cat b))
>     pId' : (x : obj cat) -> mapMor (x, b) (x, b) (MkProductMorphism (identity cat x) (identity cat b)) = identity cat (mapObj (x, b))
>     pId' x = pId (x, b)
>     pComp' : (x, y, z : obj cat) -> (f : mor cat x y) -> (g : mor cat y z) 
>           -> mapMor (x, b) (z, b) (MkProductMorphism (compose cat x y z f g) (identity cat b))
>            = compose cat (mapObj (x, b)) (mapObj (y, b)) (mapObj (z, b)) (mapMor (x, b) (y, b) (MkProductMorphism f (identity cat b))) (mapMor (y, b) (z, b) (MkProductMorphism g (identity cat b)))
>     pComp' x y z f g = 
>       replace {P=\q=>mapMor (x, b) (z, b) (MkProductMorphism (compose cat x y z f g) q) = compose cat (mapObj (x, b)) (mapObj (y, b)) (mapObj (z, b)) (mapMor (x, b) (y, b) (MkProductMorphism f (identity cat b))) (mapMor (y, b) (z, b) (MkProductMorphism g (identity cat b)))} 
>               (leftIdentity cat b b (identity cat b)) 
>               (pComp (x,b) (y,b) (z,b) (MkProductMorphism f (identity cat b)) (MkProductMorphism g (identity cat b)))

Andre: seems like I got disconnected from the call and now nothing loads...
We can read you tho, try reconnecting on zoom!
use the link nin the issue?
use the force!
I'm so confused: zoom doesn't work in chrome and safari, and rocketchat is also not connecting, but I can view twitch just fine...
Oldest trick in the world: Reboot
I

wth @andreK ???




id_b ; id_b --> idb


(-,b) --> (-,b)

(id_a,id_b) --> id_{a x b}


cat x cat -F-> cat 



fun (a,b)
     MkCFunctor ?mo ?mm ?pid ?pco

> parameters (cat : Category, products : catHasProducts cat, terminal : catHasTerminalObj cat)
>   rightUnitorComponent : (a : obj cat) -> mor cat (carrier $ products a (carrier terminal)) a
>   rightUnitorComponent a = Product.pi1 $ products a (carrier terminal)


rightUnitor: ( - ) x 1 --> id cat

rightUnitor_A : A x 1 -- pi1 -> A

A x 1 --- pi1 ---> A
    |                        |
    |                        |
  <pi1;f , pi2>      f
    |                        |
    |                       \ /
B x 1 --- pi1 ---> B


<pi1,pi2> = id_{AxB}