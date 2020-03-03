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
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> ExtensionalTypeMorphism c (Pair a b)
> applyLeftAndRight a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) =
>   (MkExtensionalTypeMorphism (\c => (f c, g c)))
>
> leftCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> extCompose c (Pair a b) a (applyLeftAndRight a b c f g) (MkExtensionalTypeMorphism Prelude.Basics.fst) = f
> leftCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> rightCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> extCompose c (Pair a b) b (applyLeftAndRight a b c f g) (MkExtensionalTypeMorphism Prelude.Basics.snd) = g
> rightCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> surjective_pairing : (c : (a, b))
>                   -> (c = (fst c, snd c))
> surjective_pairing (a, b) = Refl
>
> injective_projections : (p1 : (a, b)) -> (p2 : (a, b))
>                      -> Prelude.Basics.fst p1 = Prelude.Basics.fst p2
>                      -> Prelude.Basics.snd p1 = Prelude.Basics.snd p2
>                      -> p1 = p2
> injective_projections (a, b) p2 hfst hsnd =
>   rewrite hfst in
>   rewrite hsnd in
>   rewrite (surjective_pairing p2) in
>   Refl
>
> equal_assoc : a = b -> b = a
> equal_assoc Refl = Refl
>
> extensionalTypeMorphismEq : MkExtensionalTypeMorphism x = MkExtensionalTypeMorphism y
>                          -> x = y
>
> unique :
>      (f : ExtensionalTypeMorphism c a)
>   -> (g : ExtensionalTypeMorphism c b)
>   -> (h : ExtensionalTypeMorphism c (Pair a b))
>   -> (commutativityLeft : extCompose c (Pair a b) a h (MkExtensionalTypeMorphism Prelude.Basics.fst) = f)
>   -> (commutativityRight: extCompose c (Pair a b) b h (MkExtensionalTypeMorphism Prelude.Basics.snd) = g)
>   -> h = applyLeftAndRight a b c f g
> unique (MkExtensionalTypeMorphism f)
>        (MkExtensionalTypeMorphism g)
>        (MkExtensionalTypeMorphism h)
>        commutativityLeft
>        commutativityRight =
>   funExt(\x =>
>     rewrite surjective_pairing (h x) in
>     rewrite injective_projections
>               (fst (h x), snd (h x))
>               (f x, g x)
>               (rewrite equal_assoc (extensionalTypeMorphismEq commutativityLeft) in Refl)
>               (rewrite equal_assoc (extensionalTypeMorphismEq commutativityRight) in Refl) in
>     Refl
>   )
>
> pairToProduct : (a, b : Type) -> Product Idris.TypesAsCategoryExtensional.typesAsCategoryExtensional a b
> pairToProduct a b = MkCoProduct
>   (Pair a b)
>   (MkExtensionalTypeMorphism Prelude.Basics.fst)
>   (MkExtensionalTypeMorphism Prelude.Basics.snd)
>   (\c, f, g => MkCommutingMorphism (applyLeftAndRight a b c f g) (leftCompose a b c f g) (rightCompose a b c f g))
>   (\c, f, g, h => unique f g (challenger h) (commutativityLeft h) (commutativityRight h))
