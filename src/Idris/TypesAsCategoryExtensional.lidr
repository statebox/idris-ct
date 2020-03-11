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

> module Idris.TypesAsCategoryExtensional
>
> import Basic.Category
>
> %access public export
> %default total
>
> record ExtensionalTypeMorphism (a : Type) (b : Type) where
>   constructor MkExtensionalTypeMorphism
>   func : a -> b
>
> extensionalTypeMorphismEq : MkExtensionalTypeMorphism x = MkExtensionalTypeMorphism y -> x = y
> extensionalTypeMorphismEq Refl = Refl
>
> postulate
> funExt : {f, g : ExtensionalTypeMorphism a b} -> ((x : a) -> func f x = func g x) -> f = g
>
> extIdentity : (a : Type) -> ExtensionalTypeMorphism a a
> extIdentity a = MkExtensionalTypeMorphism id
>
> extCompose :
>      (a, b, c : Type)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> ExtensionalTypeMorphism a c
> extCompose a b c (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g)
>   = MkExtensionalTypeMorphism (g . f)
>
> funcPreserveCompose :
>      {a, b, c : Type}
>   -> (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> func (extCompose a b c f g) = func g . func f
> funcPreserveCompose (MkExtensionalTypeMorphism f) (MkExtensionalTypeMorphism g) = Refl
>
> extLeftIdentity :
>      (a, b : Type)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> extCompose a a b (extIdentity a) f = f
> extLeftIdentity a b (MkExtensionalTypeMorphism func) = Refl
>
> extRightIdentity :
>      (a, b : Type)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> extCompose a b b f (extIdentity b) = f
> extRightIdentity a b (MkExtensionalTypeMorphism func) = Refl
>
> extAssociativity :
>      (a, b, c, d : Type)
>   -> (f : ExtensionalTypeMorphism a b)
>   -> (g : ExtensionalTypeMorphism b c)
>   -> (h : ExtensionalTypeMorphism c d)
>   -> extCompose a b d f (extCompose b c d g h) = extCompose a c d (extCompose a b c f g) h
> extAssociativity a b c d (MkExtensionalTypeMorphism fun1)
>                          (MkExtensionalTypeMorphism fun2)
>                          (MkExtensionalTypeMorphism fun3) = Refl
>
> typesAsCategoryExtensional : Category
> typesAsCategoryExtensional = MkCategory
>   Type
>   ExtensionalTypeMorphism
>   extIdentity
>   extCompose
>   extLeftIdentity
>   extRightIdentity
>   extAssociativity
