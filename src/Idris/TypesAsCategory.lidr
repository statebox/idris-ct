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

> module Idris.TypesAsCategory
>
> import Basic.Category
>
> %access public export
> %default total
>
> TypeMorphism : Type -> Type -> Type
> TypeMorphism a b = a -> b
>
> identity : (a : Type) -> TypeMorphism a a
> identity a = (\x => x)
>
> compose :
>      (a, b, c : Type)
>   -> (f : TypeMorphism a b)
>   -> (g : TypeMorphism b c)
>   -> TypeMorphism a c
> compose a b c f g = g . f
>
> leftIdentity :
>      (a, b : Type)
>   -> (f : TypeMorphism a b)
>   -> f . (identity a) = f
> leftIdentity a b f = Refl
>
> rightIdentity :
>      (a, b : Type)
>   -> (f : TypeMorphism a b)
>   -> (identity b) . f = f
> rightIdentity a b f = Refl
>
> associativity :
>      (a, b, c, d : Type)
>   -> (f : TypeMorphism a b)
>   -> (g : TypeMorphism b c)
>   -> (h : TypeMorphism c d)
>   -> (h . g) . f = h . (g . f)
> associativity a b c d f g h = Refl
>
> typesAsCategory : Category
> typesAsCategory = MkCategory
>   Type
>   TypeMorphism
>   identity
>   compose
>   leftIdentity
>   rightIdentity
>   associativity
