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

> module Idris.EitherAsCoProduct
>
> import Idris.TypesAsCategoryExtensional
>
> import Basic.Category
> import CoLimits.CoProduct
>
> applyLeftOrRight :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> ExtensionalTypeMorphism (Either a b) c
> applyLeftOrRight a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) =
>   (MkExtensionalTypeMorphism (either f g))
>
> leftCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) (applyLeftOrRight a b c f g) = f
> leftCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> rightCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) (applyLeftOrRight a b c f g) = g
> rightCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> applyExtWith :
>      (x : a)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> b
> applyExtWith x f = apply (func f) x
>
> unique :
>      (f : ExtensionalTypeMorphism a c)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> (h : ExtensionalTypeMorphism (Either a b) c)
>   -> (commutativityLeft : extCompose a (Either a b) c (MkExtensionalTypeMorphism Left) h = f)
>   -> (commutativityRight: extCompose b (Either a b) c (MkExtensionalTypeMorphism Right) h = g)
>   -> h = applyLeftOrRight a b c f g
> unique (MkExtensionalTypeMorphism f)
>        (MkExtensionalTypeMorphism g)
>        (MkExtensionalTypeMorphism h)
>        commutativityLeft
>        commutativityRight =
>   funExt(\x =>
>     case x of
>       Left l  => cong {f = applyExtWith l} commutativityLeft
>       Right r => cong {f = applyExtWith r} commutativityRight
>   )
>
> eitherToCoProduct : (a, b : Type) -> CoProduct Idris.TypesAsCategoryExtensional.typesAsCategoryExtensional a b
> eitherToCoProduct a b = MkCoProduct
>   (Either a b)
>   (MkExtensionalTypeMorphism Left)
>   (MkExtensionalTypeMorphism Right)
>   (\c, f, g => MkCommutingMorphism (applyLeftOrRight a b c f g) (leftCompose a b c f g) (rightCompose a b c f g))
>   (\c, f, g, h => unique f g (challenger h) (commutativityLeft h) (commutativityRight h))
