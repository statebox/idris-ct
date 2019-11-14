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

> module Basic.Isomorphism
>
> import Basic.Category
> import Utils
>
> %access public export
> %default total
>
> record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkIsomorphism
>   morphism : mor cat a b
>   Inverse: mor cat b a
>   lawleft: compose cat a b a morphism Inverse = identity cat a
>   lawright: compose cat b a b Inverse morphism = identity cat b
>
> isomorphismExt :
>      (cat : Category)
>   -> (a, b : obj cat)
>   -> (iso1, iso2 : Isomorphism cat a b)
>   -> (morphism iso1 = morphism iso2)
>   -> (Inverse iso1 = Inverse iso2)
>   -> trans1 = trans2
> isomorphismExt _ _ _ _ _ _ _ = really_believe_me ()
>
> idIsomorphism : (cat : Category) -> (a : obj cat) -> Isomorphism cat a a
> idIsomorphism cat a = MkIsomorphism
>   (identity cat a)
>   (identity cat a)
>   (leftIdentity cat a a (identity cat a))
>   (leftIdentity cat a a (identity cat a))
>
> isoMorphismComposition : (cat : Category) -> (a, b, c : obj cat)
>   -> Isomorphism cat a b
>   -> Isomorphism cat b c
>   -> Isomorphism cat a c
> isoMorphismComposition cat a b c iso1 iso2 = MkIsomorphism
>   (compose cat a b c (morphism iso1) (morphism iso2))
>   (compose cat c b a (Inverse iso2) (Inverse iso1))
>   (trans (associativity cat a c b a _ (Inverse iso2) (Inverse iso1))
>     (trans (cong2
>       (trans (sym (associativity cat a b c b (morphism iso1) (morphism iso2) (Inverse iso2)))
>         (trans (cong (lawleft iso2)) (rightIdentity cat a b (morphism iso1))))
>       (Refl { x = Inverse iso1 }))
>     (lawleft iso1)))
>   (trans (associativity cat c a b c _ (morphism iso1) (morphism iso2))
>     (trans (cong2
>       (trans (sym (associativity cat c b a b (Inverse iso2) (Inverse iso1) (morphism iso1)))
>         (trans (cong (lawright iso1)) (rightIdentity cat c b (Inverse iso2))))
>       (Refl { x = morphism iso2 }))
>     (lawright iso2)))
>
> isomorphismCategory : (cat : Category) -> Category
> isomorphismCategory cat = MkCategory
>   (obj cat)
>   (Isomorphism cat)
>   (idIsomorphism cat)
>   (isoMorphismComposition cat)
>   (\a, b, iso => isomorphismExt cat a b (isoMorphismComposition cat a a b (idIsomorphism cat a) iso) iso
>     (leftIdentity cat a b (morphism iso))
>     (rightIdentity cat b a (Inverse iso)))
>   (\a, b, iso => isomorphismExt cat a b (isoMorphismComposition cat a b b iso (idIsomorphism cat b)) iso
>     (rightIdentity cat a b (morphism iso))
>     (leftIdentity cat b a (Inverse iso)))
>   (\a, b, c, d, iso1, iso2, iso3 => isomorphismExt cat a d
>     (isoMorphismComposition cat a b d iso1 (isoMorphismComposition cat b c d iso2 iso3))
>     (isoMorphismComposition cat a c d (isoMorphismComposition cat a b c iso1 iso2) iso3)
>     (associativity cat a b c d (morphism iso1) (morphism iso2) (morphism iso3))
>     (sym (associativity cat d c b a (Inverse iso3) (Inverse iso2) (Inverse iso1))))
