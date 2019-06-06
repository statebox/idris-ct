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
> record CommutingMorphism (cat : Category)
>                          (x : obj cat) (a : obj cat) (b : obj cat) (carrier : obj cat)
>                          (pi1 : mor cat carrier a) (pi2 : mor cat carrier b)
>                          (f : mor cat x a) (g : mor cat x b) where
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
>   exists : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b) -> CommutingMorphism cat x a b carrier pi1 pi2 f g
>   unique : (x : obj cat) -> (f : mor cat x a) -> (g : mor cat x b)
>         -> (h : CommutingMorphism cat x a b carrier pi1 pi2 f g)
>         -> h = exists x f g
>
> productMorphism : (cat : Category) -> (a1, a2, b1, b2 : obj cat) 
>                -> (f : mor cat a1 a2) -> (g : mor cat b1 b2) 
>                -> (pr1 : Product cat a1 b1) -> (pr2 : Product cat a2 b2)
>                -> mor cat (carrier pr1) (carrier pr2)
> productMorphism cat a1 a2 b1 b2 f g pr1 pr2 = 
>   challenger $ exists pr2 prod1 (compose cat _ _ _ pi1' f) (compose cat _ _ _ pi2' g)
>     where
>       prod1 : obj cat
>       prod1 = carrier pr1
>       prod2 : obj cat
>       prod2 = carrier pr2
>       pi1' : mor cat prod1 a1
>       pi1' = pi1 pr1
>       pi2' : mor cat prod1 b1
>       pi2' = pi2 pr1
> 
> productFunctor : (cat : Category) -> (pex : (a, b : obj cat) -> Product cat a b) -> CFunctor (productCategory cat cat) cat
> productFunctor cat pex = MkCFunctor mapObj mapMor idLaw ?compLaw
>   where
>     mapObj : obj (productCategory cat cat) -> obj cat
>     mapObj (a,b) = carrier $ pex a b
>     mapMor : (a, b : obj (productCategory cat cat))
>            -> mor (productCategory cat cat) a b
>            -> mor cat (mapObj a) (mapObj b)
>     mapMor (a1,b1) (a2,b2) (MkProductMorphism f g) = 
>       productMorphism cat a1 a2 b1 b2 f g (pex a1 b1) (pex a2 b2)
>     bla : (a,b : obj cat) -> CommutingMorphism cat (carrier (pex a b)) a b (carrier (pex a b))
>                              (pi1 (pex a b))
>                              (pi2 (pex a b))
>                              (compose cat (carrier (pex a b)) a a (pi1 (pex a b)) (identity cat a))
>                              (compose cat (carrier (pex a b)) b b (pi2 (pex a b)) (identity cat b))
>     bla a b = MkCommutingMorphism (identity cat (carrier (pex a b))) 
>                            (rewrite leftIdentity cat (carrier (pex a b)) a (pi1 (pex a b)) in 
>                             sym $ rightIdentity cat (carrier (pex a b)) a (pi1 (pex a b)))
>                            (rewrite leftIdentity cat (carrier (pex a b)) b (pi2 (pex a b)) in
>                             sym $ rightIdentity cat (carrier (pex a b)) b (pi2 (pex a b)))
>     idLaw : (a : obj (productCategory cat cat)) -> mapMor a a (identity (productCategory cat cat) a) = identity cat (mapObj a)
>     idLaw (a,b) = sym $ cong {f=challenger} $ 
>                   unique (pex a b) (carrier (pex a b)) 
>                          (compose cat (carrier (pex a b)) a a (pi1 (pex a b)) (identity cat a))
>                          (compose cat (carrier (pex a b)) b b (pi2 (pex a b)) (identity cat b))
>                          (bla a b) 
>
> catHasProducts : Category -> Type
> catHasProducts cat = (a, b : obj cat) -> Product cat a b


(AxB) x C --> A x (B x C)
< pi1_{(AxB)xC};pi1_{AxB}, < pi1_{(AxB)xC};pi2_{AxB}, pi2_{(AxB)xC}> > 


    MkCFunctor
       (\(a, b) => carrier $ pex a b)
       (\(a1, b1), (a2, b2), (f, g) => productMorphism cat a1 a2 b1 b2 f g (pex a1 b1) (pex a2 b2))
       ?id
       ?comp

 catHasProducts : 

exists_a2.b2 (pi1_a1.b1;f, pi2_a1.b1;g )