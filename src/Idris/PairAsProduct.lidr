\iffalse
SPDX-License-Identifier: AGPL-3.0-only

This file is part of `idris-ct` Category Theory in Idris library.

Copyright (C) 2020 Stichting Statebox <https://statebox.nl>

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

> module Idris.PairAsProduct
>
> import Idris.TypesAsCategoryExtensional
>
> import Basic.Category
> import Limits.Product
>
> %access public export
> %default total
>
> applyLeftAndRight :
>      (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> ExtensionalTypeMorphism c (Pair a b)
> applyLeftAndRight (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) =
>   (MkExtensionalTypeMorphism (\x => (f x, g x)))
>
> leftCompose :
>      (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> extCompose c (Pair a b) a (applyLeftAndRight f g) (MkExtensionalTypeMorphism Basics.fst) = f
> leftCompose (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> rightCompose :
>      (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> extCompose c (Pair a b) b (applyLeftAndRight f g) (MkExtensionalTypeMorphism Basics.snd) = g
> rightCompose (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> surjectivePairing : (c : (a, b)) -> c = (fst c, snd c)
> surjectivePairing (a, b) = Refl
>
> injectiveProjections :
>      (p1, p2 : (a, b))
>   -> Basics.fst p1 = Basics.fst p2
>   -> Basics.snd p1 = Basics.snd p2
>   -> p1 = p2
> injectiveProjections (a, b) p2 hfst hsnd =
>   rewrite hfst in
>   rewrite hsnd in
>   rewrite (surjectivePairing p2) in
>   Refl
>
> unique :
>      (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> (h : ExtensionalTypeMorphism c (Pair a b))
>   -> (commutativityLeft : extCompose c (Pair a b) a h (MkExtensionalTypeMorphism Basics.fst) = f)
>   -> (commutativityRight: extCompose c (Pair a b) b h (MkExtensionalTypeMorphism Basics.snd) = g)
>   -> h = applyLeftAndRight f g
> unique (MkExtensionalTypeMorphism f)
>        (MkExtensionalTypeMorphism g)
>        (MkExtensionalTypeMorphism h)
>        commutativityLeft
>        commutativityRight =
>   funExt(\x =>
>     rewrite surjectivePairing (h x) in
>     rewrite injectiveProjections
>             (fst (h x), snd (h x))
>             (f x, g x)
>             (rewrite sym (extensionalTypeMorphismEq commutativityLeft) in Refl)
>             (rewrite sym (extensionalTypeMorphismEq commutativityRight) in Refl) in
>     Refl
>   )
>
> pairToProduct : (a, b : Type) -> Product TypesAsCategoryExtensional.typesAsCategoryExtensional a b
> pairToProduct a b = MkCoProduct
>   (Pair a b)
>   (MkExtensionalTypeMorphism Prelude.Basics.fst)
>   (MkExtensionalTypeMorphism Prelude.Basics.snd)
>   (\c, f, g => MkCommutingMorphism (applyLeftAndRight f g) (leftCompose f g) (rightCompose f g))
>   (\c, f, g, h => unique f g (challenger h) (commutativityLeft h) (commutativityRight h))
