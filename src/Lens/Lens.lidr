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

> module Lens.Lens
>
> import Basic.Category
>
> %access public export
> %default total
>
> record Lens (s : Type) (t : Type) (a : Type) (b : Type) where
>   constructor MkLens
>   get : s -> a
>   put : (s, b) -> t
>
> identityLens : Lens s t s t
> identityLens = MkLens id snd
>
> lensComposition : Lens s t a b -> Lens a b c d  -> Lens s t c d
> lensComposition outerLens innerLens = MkLens
>   (get innerLens . get outerLens)
>   (\sd => put outerLens (fst sd, (put innerLens ((get outerLens (fst sd)), (snd sd)))))
>
> -- TODO: can we do better than this?
> postulate
> funExtOnPairs : (f : (a, b) -> c) -> (\xy => f (fst xy, snd xy)) = f
>
> lensesAsCategory : Category
> lensesAsCategory = MkCategory
>   (Type, Type)
>   (\st, ab => Lens (fst st) (snd st) (fst ab) (snd ab))
>   (\st => identityLens {s = fst st} {t = snd st})
>   (\_, _, _ => lensComposition)
>   (\_, _, (MkLens g p) => rewrite (funExtOnPairs p) in Refl)
>   (\_, _, (MkLens g p) => rewrite (funExtOnPairs p) in Refl)
>   (\_, _, _, _, _, _, _ => Refl)
