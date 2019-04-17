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

> module Monoid.MonoidMorphism
>
> import Monoid.Monoid
>
> -- contrib
> import Interfaces.Verified
>
> %access public export
> %default total
>
> record MonoidMorphism (domain : Monoid) (codomain : Monoid) where
>   constructor MkMonoidMorphism
>   func       : set domain -> set codomain
>   funcRespOp : (a, b : set domain)
>             -> func ((<+>) @{verifiedMonoidToSemigroup @{axioms domain}} a b)
>              = (<+>) @{verifiedMonoidToSemigroup @{axioms codomain}} (func a) (func b)
>   funcRespId : func (neutral @{verifiedMonoidToMonoid @{axioms domain}})
>              = neutral @{verifiedMonoidToMonoid @{axioms codomain}}
>
> monoidMorphismEq :
>      (mor1, mor2 : MonoidMorphism m1 m2)
>   -> ((x : set m1) -> (func mor1 x) = (func mor2 x))
>   -> mor1 = mor2
> monoidMorphismEq mor1 mor2 pointWisePrf = really_believe_me pointWisePrf
>
> monoidIdentity : (m : Monoid) -> MonoidMorphism m m
> monoidIdentity m = MkMonoidMorphism
>   id
>   (\_, _ => Refl)
>   Refl
>
> monoidMorphismsComposition :
>      MonoidMorphism a b
>   -> MonoidMorphism b c
>   -> MonoidMorphism a c
> monoidMorphismsComposition mor1 mor2 =
>   MkMonoidMorphism
>     ((func mor2) . (func mor1))
>     (\a, b => trans (cong {f = func mor2} (funcRespOp mor1 a b)) (funcRespOp mor2 (func mor1 a) (func mor1 b)))
>     (trans (cong {f = func mor2} (funcRespId mor1)) (funcRespId mor2))
