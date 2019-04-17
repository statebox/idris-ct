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

> module Monoid.MonoidsCategory
>
> import Basic.Category
> import Monoid.Monoid
> import Monoid.MonoidMorphism
> import Utils
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> monoidsLeftIdentity :
>      (m1, m2 : Monoid)
>   -> (mor : MonoidMorphism m1 m2)
>   -> monoidMorphismsComposition (monoidIdentity m1) mor = mor
> monoidsLeftIdentity m1 m2 mor = monoidMorphismEq
>   (monoidMorphismsComposition (monoidIdentity m1) mor)
>   mor
>   (\x => Refl)
>
> monoidRightIdentity :
>      (m1, m2 : Monoid)
>   -> (mor : MonoidMorphism m1 m2)
>   -> monoidMorphismsComposition mor (monoidIdentity m2) = mor
> monoidRightIdentity m1 m2 mor = monoidMorphismEq
>   (monoidMorphismsComposition mor (monoidIdentity m2))
>   mor
>   (\x => Refl)
>
> monoidAssociativity :
>      (m1, m2, m3, m4 : Monoid)
>   -> (mor1 : MonoidMorphism m1 m2)
>   -> (mor2 : MonoidMorphism m2 m3)
>   -> (mor3 : MonoidMorphism m3 m4)
>   -> monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3)
>    = monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3
> monoidAssociativity m1 m2 m3 m4 mor1 mor2 mor3 = monoidMorphismEq
>   (monoidMorphismsComposition mor1 (monoidMorphismsComposition mor2 mor3))
>   (monoidMorphismsComposition (monoidMorphismsComposition mor1 mor2) mor3)
>   (\x => Refl)
>
> monoidsCategory : Category
> monoidsCategory = MkCategory
>   Monoid
>   MonoidMorphism
>   monoidIdentity
>   (\m1, m2, m3 => monoidMorphismsComposition {a = m1} {b = m2} {c = m3})
>   monoidsLeftIdentity
>   monoidRightIdentity
>   monoidAssociativity
