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

> module PointedTypes.PointedTypesAsCategory
>
> import Basic.Category
>
> %access public export
> %default total
>
> PointedObject : Type
> PointedObject = (a : Type ** a)
>
> record PointedMorphism (a : PointedObject) (b : PointedObject) where
>   constructor MkPointedMorphism
>   func : (fst a) -> (fst b)
>   funcRespPoint : func (snd a) = snd b
>
> pointedIdentity : (a : PointedObject) -> PointedMorphism a a
> pointedIdentity (a' ** x) = MkPointedMorphism id Refl
>
> compose : (a, b, c : PointedObject) -> (f : PointedMorphism a b) -> (g : PointedMorphism b c) -> PointedMorphism a c
> compose
>   (a' ** x)
>   (b' ** y)
>   (c' ** z)
>   (MkPointedMorphism f' fxy)
>   (MkPointedMorphism g' gyz)
>   = MkPointedMorphism (g' . f') (trans (cong {f = g'} fxy) gyz)
>
> leftReflId : (p : x = y) -> trans Refl p = p
> leftReflId Refl = Refl
>
> pointedLeftIdentity :
>      (a, b : PointedObject)
>   -> (f : PointedMorphism a b)
>   -> compose a a b (pointedIdentity a) f = f
> pointedLeftIdentity
>   (a' ** x)
>   (b' ** y)
>   (MkPointedMorphism f' fxy)
>   = cong {f = MkPointedMorphism f'} (leftReflId fxy)
>
> rightReflId : (p : x = y) -> trans p Refl = p
> rightReflId Refl = Refl
>
> congId : (p : x = y) -> cong {f = Basics.id} p = p
> congId Refl = Refl
>
> pointedRightIdentity :
>      (a, b : PointedObject)
>   -> (f : PointedMorphism a b)
>   -> compose a b b f (pointedIdentity b) = f
> pointedRightIdentity
>   (a' ** x)
>   (b' ** y)
>   (MkPointedMorphism f' fxy)
>   = cong {f = MkPointedMorphism f'} (trans (rightReflId (cong {f = id} fxy)) (congId fxy))
>
> transCongAssociacivity :
>      (f : a -> b)
>   -> (g : b -> c)
>   -> (h : c -> d)
>   -> (fxy : f x = y)
>   -> (gyw : g y = w)
>   -> (hwz : h w = z)
>   -> trans
>       (cong {f = h . g} fxy)
>       (trans (cong {f = h} gyw) hwz)
>     = trans
>       (cong {f = h} (trans (cong {f = g} fxy) gyw)) hwz
> transCongAssociacivity f g h Refl Refl Refl = Refl
>
> pointedAssociativity :
>      (a, b, c, d : PointedObject)
>   -> (f : PointedMorphism a b)
>   -> (g : PointedMorphism b c)
>   -> (h : PointedMorphism c d)
>   -> compose a b d f (compose b c d g h) = compose a c d (compose a b c f g) h
> pointedAssociativity
>   (a' ** x)
>   (b' ** y)
>   (c' ** w)
>   (d' ** z)
>   (MkPointedMorphism f' fxy)
>   (MkPointedMorphism g' gyw)
>   (MkPointedMorphism h' hwz)
>   = cong {f = MkPointedMorphism (h' . g' . f')} (transCongAssociacivity f' g' h' fxy gyw hwz)
>
> pointedTypesCategory : Category
> pointedTypesCategory = MkCategory
>   PointedObject
>   PointedMorphism
>   pointedIdentity
>   compose
>   pointedLeftIdentity
>   pointedRightIdentity
>   pointedAssociativity
