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

> module Discrete.DiscreteCategory
>
> import Basic.Category
>
> %access public export
> %default total
>
> DiscreteMorphism : (x, y : a) -> Type
> DiscreteMorphism x y = x = y
>
> discreteIdentity : (x : a) -> DiscreteMorphism x x
> discreteIdentity _ = Refl
>
> discreteCompose : (x, y, z : a) -> DiscreteMorphism x y -> DiscreteMorphism y z -> DiscreteMorphism x z
> discreteCompose _ _ _ Refl Refl = Refl
>
> discreteLeftIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x x y (discreteIdentity x) f = f
> discreteLeftIdentity _ _ Refl = Refl
>
> discreteRightIdentity : (x, y : a) -> (f : DiscreteMorphism x y) -> discreteCompose x y y f (discreteIdentity y) = f
> discreteRightIdentity _ _ Refl = Refl
>
> discreteAssociativity : (w, x, y, z : a)
>                      -> (f : DiscreteMorphism w x)
>                      -> (g : DiscreteMorphism x y)
>                      -> (h : DiscreteMorphism y z)
>                      -> discreteCompose w x z f (discreteCompose x y z g h)
>                       = discreteCompose w y z (discreteCompose w x y f g) h
> discreteAssociativity _ _ _ _ Refl Refl Refl = Refl
>
> discreteCategory : (a : Type) -> Category
> discreteCategory a = MkCategory
>   a
>   DiscreteMorphism
>   discreteIdentity
>   discreteCompose
>   discreteLeftIdentity
>   discreteRightIdentity
>   discreteAssociativity
