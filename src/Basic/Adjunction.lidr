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

> module Basic.Adjunction
>
> import Basic.Category as Cat
> import Basic.Functor
> import Basic.Isomorphism
> import Basic.NaturalTransformation
> import Cats.CatsAsCategory
> import Cats.FunctorsAsCategory
> import Idris.TypesAsCategory as Idris
> import Utils
>
> %access public export
> %default total
>
> record Adjunction
>   (cat1 : Category)
>   (cat2 : Category)
>   (funL : CFunctor cat2 cat1)
>   (funR : CFunctor cat1 cat2)
> where
>   constructor MkAdjunction
>   homIsomorphism : (a : obj cat2)
>                 -> (b : obj cat1)
>                 -> Isomorphism Idris.typesAsCategory (mor cat1 (mapObj funL a) b) (mor cat2 a (mapObj funR b))
>   commutativity : {a, a' : obj cat2}
>                -> {b, b' : obj cat1}
>                -> (f: mor cat2 a' a)
>                -> (g: mor cat1 b b')
>                -> (h: mor cat1 (mapObj funL a) b)
>                -> compose cat2 a' a (mapObj funR b') f
>                     (compose cat2 a (mapObj funR b) (mapObj funR b')
>                       (morphism (homIsomorphism a b) h) (mapMor funR b b' g))
>                 = morphism (homIsomorphism a' b')
>                     (compose cat1 (mapObj funL a') (mapObj funL a) b'
>                       (mapMor funL a' a f) (compose cat1 (mapObj funL a) b b' h g))
>
> adjunctionInverseCommutativity :
>        {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> (adj: Adjunction cat1 cat2 funL funR)
>     -> {a, a' : obj cat2}
>     -> {b, b' : obj cat1}
>     -> (f: mor cat2 a' a)
>     -> (g: mor cat1 b b')
>     -> (h: mor cat2 a (mapObj funR b))
>     -> compose cat1 (mapObj funL a') (mapObj funL a) b' (mapMor funL a' a f)
>          (compose cat1 (mapObj funL a) b b'
>            (Inverse (homIsomorphism adj a b) h) g)
>      = Inverse (homIsomorphism adj a' b')
>          (compose cat2 a' a (mapObj funR b')
>            f (compose cat2 a (mapObj funR b) (mapObj funR b') h (mapMor funR b b' g)))
> adjunctionInverseCommutativity {cat1} {cat2} {funL} {funR} (MkAdjunction iso comm) {a} {a'} {b} {b'} f g h = ?t
>
> unit : {cat1, cat2 : Category}
>     -> {funL : CFunctor cat2 cat1}
>     -> {funR : CFunctor cat1 cat2}
>     -> Adjunction cat1 cat2 funL funR
>     -> NaturalTransformation cat2 cat2 (idFunctor cat2) (functorComposition cat2 cat1 cat2 funL funR)
> unit {cat1} {cat2} {funL} {funR} (MkAdjunction iso comm) = MkNaturalTransformation
>   (\a => morphism (iso a (mapObj funL a)) (identity cat1 (mapObj funL a)))
>   (\a, b, f =>
>     trans (sym (leftIdentity cat2 a _ _))
>     (trans (comm (identity cat2 a) (mapMor funL a b f) (identity cat1 (mapObj funL a)))
>     (trans (cong
>       (trans (cong2 (preserveId funL a) (Refl { x = compose cat1 _ _ _ (identity cat1 (mapObj funL a)) (mapMor funL a b f) }))
>       (trans (leftIdentity cat1 (mapObj funL a) _ _)
>       (trans (leftIdentity cat1 (mapObj funL a) _ _)
>       (trans (sym (rightIdentity cat1 _ _ _))
>       (cong (sym (rightIdentity cat1 (mapObj funL b) _ _))))))))
>     (trans (sym (comm f (identity cat1 (mapObj funL b)) (identity cat1 (mapObj funL b))))
>     (cong (trans (cong (preserveId funR _)) (rightIdentity cat2 _ _ _)))))))
>
> counit : {cat1, cat2 : Category}
>       -> {funL : CFunctor cat2 cat1}
>       -> {funR : CFunctor cat1 cat2}
>       -> Adjunction cat1 cat2 funL funR
>       -> NaturalTransformation cat1 cat1 (functorComposition cat1 cat2 cat1 funR funL) (idFunctor cat1)
> counit {cat1} {cat2} {funL} {funR} (MkAdjunction iso comm) = MkNaturalTransformation
>   (\b => Inverse (iso (mapObj funR b) b) (identity cat2 (mapObj funR b)))
>   (\a, b, f => ?x)


compose cat1 (mapObj funL (mapObj funR a)) a b
  (Inverse (iso (mapObj funR a) a) (identity cat2 (mapObj funR a)))
  f =
compose cat1 (mapObj funL (mapObj funR a)) (mapObj funL (mapObj funR b)) b
  (mapMor funL (mapObj funR a) (mapObj funR b) (mapMor funR a b f))
  (Inverse (iso (mapObj funR b) b) (identity cat2 (mapObj funR b)))

f . (phi h . funR g) = phi (funL f . (h . g))

inv id_funRa . f = funL (funR f) . inv id_funRb



phi id_funLa . funR (funL f) = f . phi id_funLb

id_a . (phi id_funLa . funR (funL f)) = phi (funL id_a . (id_funLa . funL f))
f . (phi id_funLb . funR id_funLb) = phi (funL f . (id_funLb . id_funLb))
