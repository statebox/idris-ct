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

> module Limits.MonoidalProduct
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Basic.NaturalIsomorphism
> import Product.ProductCategory
> import Limits.TerminalObject
> import Limits.Product
>
> %access public export
> %default total
> %auto_implicits off
>
> parameters (cat : Category, product : catHasProducts cat, terminal : TerminalObject cat)
>   commutativeIdentity :
>        (a, b : obj cat)
>     -> let pab = product a b in
>        CommutingMorphism cat (carrier pab) a b (carrier pab) (pi1 pab) (pi2 pab) (pi1 pab) (pi2 pab)
>   commutativeIdentity a b =
>     MkCommutingMorphism (identity cat $ carrier $ product a b)
>                         (leftIdentity cat (carrier $ product a b) a (pi1 $ product a b))
>                         (leftIdentity cat (carrier $ product a b) b (pi2 $ product a b))
>
>   productPi12Identity :
>        (a, b : obj cat)
>     -> let pab = product a b in
>        challenger $ Product.exists pab (carrier pab) (pi1 pab) (pi2 pab) = identity cat (carrier pab)
>   productPi12Identity a b = sym $ unique (product a b)
>                                          (carrier $ product a b)
>                                          (pi1 $ product a b)
>                                          (pi2 $ product a b)
>                                          (commutativeIdentity a b)
>
>   rightUnitorComponent : (a : obj cat) -> mor cat (carrier $ product a (carrier terminal)) a
>   rightUnitorComponent a = Product.pi1 $ product a (carrier terminal)
>
>   rightUnitorComm :
>        (a, b : obj cat)
>     -> (f : mor cat a b)
>     -> compose cat _ _ _ (rightUnitorComponent a) f
>      = compose cat _ _ _ (mapMor (bifunctorLeft cat (productFunctor cat product) (carrier terminal)) a b f)
>                          (rightUnitorComponent b)
>   rightUnitorComm a b f =
>     rewrite
>       rightIdentity cat (carrier $ product a (carrier terminal))
>                         (carrier terminal)
>                         (pi2 $ product a (carrier terminal))
>     in
>       sym $ commutativityLeft (exists (product b (carrier terminal))
>                                       (carrier $ product a (carrier terminal))
>                                       (compose cat (carrier $ product a (carrier terminal))
>                                                    a b
>                                                    (pi1 $ product a (carrier terminal))
>                                                    f)
>                                       (pi2 $ product a (carrier terminal)))
>
>   rightUnitorNatTrans : NaturalTransformation cat cat
>                                               (bifunctorLeft cat (productFunctor cat product) (carrier terminal))
>                                               (idFunctor cat)
>   rightUnitorNatTrans = MkNaturalTransformation rightUnitorComponent rightUnitorComm
>
>   rightUnitorInverse : (a : obj cat) -> mor cat a (carrier $ product a (carrier terminal))
>   rightUnitorInverse a = challenger $ Product.exists (product a (carrier terminal))
>                                                      a
>                                                      (identity cat a)
>                                                      (exists terminal a)
>
  
  doesn't seem necessary
 
  potentialIdentity :
       (a : obj cat)
    -> mor cat (carrier $ product a (carrier terminal)) (carrier $ product a (carrier terminal))
  potentialIdentity a = compose cat
              (carrier $ product a (carrier terminal))
              a
              (carrier $ product a (carrier terminal))
              (pi1 $ product a (carrier terminal))
              (challenger (exists (product a (carrier terminal)) a (identity cat a) (exists terminal a)))

>
>   rightUnitorIsomorphism : (a : obj cat) -> Isomorphism cat _ _ (rightUnitorComponent a)
>   rightUnitorIsomorphism a = MkIsomorphism (rightUnitorInverse a)
>     (rewrite sym $ productPi12Identity a (carrier terminal) in 
>      Product.unique 
>             (product a (carrier terminal))
>             (carrier $ product a (carrier terminal)) 
>             (pi1 $ product a (carrier terminal)) 
>             (pi2 $ product a (carrier terminal))
>             (MkCommutingMorphism 
>                (compose cat
>                        (carrier $ product a (carrier terminal))
>                         a
>                        (carrier $ product a (carrier terminal))
>                        (pi1 $ product a (carrier terminal))
>                        (challenger $ exists (product a (carrier terminal)) a (identity cat a) (exists terminal a))
>                ) 
>                (rewrite sym $ associativity cat (carrier $ product a (carrier terminal))
>                                                  a
>                                                 (carrier $ product a (carrier terminal)) 
>                                                  a 
>                                                 (pi1 $ product a (carrier terminal))
>                                                 (challenger (exists (product a (carrier terminal)) a (identity cat a) (exists terminal a)))
>                                                 (pi1 $ product a (carrier terminal)) in
>                 rewrite commutativityLeft $ Product.exists (product a (carrier terminal)) a (identity cat a) (exists terminal a) in
>                 rightIdentity cat (carrier $ product a (carrier terminal)) a (pi1 $ product a (carrier terminal))
>                ) 
>                (TerminalObject.unique terminal (carrier $ product a (carrier terminal)) 
>                   (compose cat
>                           (carrier $ product a (carrier terminal))
>                           (carrier $ product a (carrier terminal))
>                           (carrier terminal)
>                           (compose cat
>                                    (carrier $ product a (carrier terminal))
>                                    a
>                                    (carrier $ product a (carrier terminal))
>                                    (pi1 $ product a (carrier terminal))
>                                    (challenger $ exists (product a (carrier terminal)) a (identity cat a) (exists terminal a)))
>                           (pi2 $ product a (carrier terminal)))
>                  (pi2 $ product a (carrier terminal))
>                )
>           )
>     )
>     (commutativityLeft $ Product.exists (product a (carrier terminal)) a (identity cat a) (exists terminal a))
>
>   rightUnitorNatIso : NaturalIsomorphism cat cat (bifunctorLeft cat (productFunctor cat product) (carrier terminal))
>                                                  (idFunctor cat)
>   rightUnitorNatIso = MkNaturalIsomorphism rightUnitorNatTrans rightUnitorIsomorphism
>
>   leftUnitorComponent : (a : obj cat) -> mor cat (carrier $ product (carrier terminal) a) a
>   leftUnitorComponent a = Product.pi2 $ product (carrier terminal) a
>
>   leftUnitorComm :
>        (a, b : obj cat)
>     -> (f : mor cat a b)
>     -> compose cat _ _ _ (leftUnitorComponent a) f
>      = compose cat _ _ _ (mapMor (bifunctorRight cat (productFunctor cat product) (carrier terminal)) a b f)
>                          (leftUnitorComponent b)
>   leftUnitorComm a b f = 
>     rewrite
>       rightIdentity cat (carrier $ product (carrier terminal) a)
>                         (carrier terminal)
>                         (pi1 $ product (carrier terminal) a)
>      in
>       sym $ commutativityRight (exists (product (carrier terminal) b)
>                                        (carrier $ product (carrier terminal) a)
>                                        (pi1 $ product (carrier terminal) a)
>                                        (compose cat (carrier $ product (carrier terminal) a)
>                                                     a b
>                                                     (pi2 $ product (carrier terminal) a)
>                                                     f))
>
>   leftUnitorNatTrans : NaturalTransformation cat cat
>                                               (bifunctorRight cat (productFunctor cat product) (carrier terminal))
>                                               (idFunctor cat)
>   leftUnitorNatTrans = MkNaturalTransformation leftUnitorComponent leftUnitorComm
>
>   leftUnitorInverse : (a : obj cat) -> mor cat a (carrier $ product (carrier terminal) a)
>   leftUnitorInverse a = challenger $ Product.exists (product (carrier terminal) a)
>                                                     a
>                                                     (exists terminal a)
>                                                     (identity cat a)
>
>   leftUnitorIsomorphism : (a : obj cat) -> Isomorphism cat _ _ (leftUnitorComponent a)
>   leftUnitorIsomorphism a = MkIsomorphism (leftUnitorInverse a) 
>     (rewrite sym $ productPi12Identity (carrier terminal) a in 
>      Product.unique 
>             (product (carrier terminal) a)
>             (carrier $ product (carrier terminal) a) 
>             (pi1 $ product (carrier terminal) a) 
>             (pi2 $ product (carrier terminal) a)
>             (MkCommutingMorphism 
>                (compose cat
>                         (carrier $ product (carrier terminal) a)
>                         a
>                         (carrier $ product (carrier terminal) a)
>                         (pi2 $ product (carrier terminal) a)
>                         (challenger $ exists (product (carrier terminal) a) a (exists terminal a) (identity cat a))
>                )
>                (TerminalObject.unique terminal (carrier $ product (carrier terminal) a) 
>                   (compose cat
>                           (carrier $ product (carrier terminal) a)
>                           (carrier $ product (carrier terminal) a)
>                           (carrier terminal)
>                           (compose cat
>                                    (carrier $ product (carrier terminal) a)
>                                    a
>                                    (carrier $ product (carrier terminal) a)
>                                    (pi2 $ product (carrier terminal) a)
>                                    (challenger $ exists (product (carrier terminal) a) a (exists terminal a) (identity cat a)))
>                           (pi1 $ product (carrier terminal) a))
>                  (pi1 $ product (carrier terminal) a)
>                )
>                (rewrite sym $ associativity cat (carrier $ product (carrier terminal) a)
>                                                  a
>                                                 (carrier $ product (carrier terminal) a) 
>                                                  a 
>                                                 (pi2 $ product (carrier terminal) a)
>                                                 (challenger $ exists (product (carrier terminal) a) a (exists terminal a) (identity cat a))
>                                                 (pi2 $ product (carrier terminal) a) in
>                 rewrite commutativityRight $ Product.exists (product (carrier terminal) a) a (exists terminal a) (identity cat a)  in
>                 rightIdentity cat (carrier $ product (carrier terminal) a) a (pi2 $ product (carrier terminal) a)
>                )
>             )
>     ) 
>     (commutativityRight $ Product.exists (product (carrier terminal) a) a (exists terminal a) (identity cat a))
>
>   leftUnitorNatIso : NaturalIsomorphism cat cat (bifunctorRight cat (productFunctor cat product) (carrier terminal))
>                                                 (idFunctor cat)
>   leftUnitorNatIso = MkNaturalIsomorphism leftUnitorNatTrans leftUnitorIsomorphism
>
>   infixr 4 <**>
>
>   (<**>) : obj cat -> obj cat -> obj cat
>   (<**>) a b = carrier $ product a b
> 
>   associatorComponent : (a, b, c : obj cat) -> mor cat ((a <**> b) <**> c) (a <**> (b <**> c))
>   associatorComponent a b c = 
>     challenger $ Product.exists (product a (b <**> c)) ((a <**> b) <**> c) 
>       (compose cat ((a <**> b) <**> c) (a <**> b) a 
>                    (pi1 $ product (a <**> b) c) 
>                    (pi1 $ product a b))
>       (challenger $ Product.exists (product b c) ((a <**> b) <**> c)
>        (compose cat ((a <**> b) <**> c) (a <**> b) b
>                     (pi1 $ product (a <**> b) c) 
>                     (pi2 $ product a b))
>        (pi2 $ product (a <**> b) c))
>
>   associatorInvComponent : (a, b, c : obj cat) -> mor cat (a <**> (b <**> c)) ((a <**> b) <**> c) 
>   associatorInvComponent a b c = 
>     challenger $ Product.exists (product (a <**> b) c) (a <**> (b <**> c)) 
>       (challenger $ Product.exists (product a b) (a <**> (b <**> c))
>        (pi1 $ product a (b <**> c))
>        (compose cat (a <**> (b <**> c)) (b <**> c) b
>                     (pi2 $ product a (b <**> c)) 
>                     (pi1 $ product b c)))
>       (compose cat (a <**> (b <**> c)) (b <**> c) c 
>                    (pi2 $ product a (b <**> c)) 
>                    (pi2 $ product b c))

* Prove they are isomorphisms (Horrible)
* Prove they define a natural transformation
* Prove Triangle identity
* Prove Pentagon identity (Horrible too) 

