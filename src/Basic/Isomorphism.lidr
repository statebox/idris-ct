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
> %auto_implicits off
>
> LeftInverse : {cat : Category} -> {a, b : obj cat} -> mor cat a b -> mor cat b a -> Type
> LeftInverse {cat} {a} {b} morphism inverse = compose cat a b a morphism inverse = identity cat a
>
> RightInverse : {cat : Category} -> {a, b : obj cat} -> mor cat a b -> mor cat b a -> Type
> RightInverse {cat} {a} {b} morphism inverse = compose cat b a b inverse morphism = identity cat b
>
> record InverseMorphisms (cat : Category)
>                         (a : obj cat)
>                         (b : obj cat)
>                         (morphism : mor cat a b)
>                         (inverse : mor cat b a)
> where
>   constructor MkInverseMorphisms
>   lawLeft  : LeftInverse  morphism inverse
>   lawRight : RightInverse morphism inverse
>
> record Isomorphism (cat : Category) (a : obj cat) (b : obj cat) (morphism : mor cat a b) where
>   constructor MkIsomorphism
>   inverse : mor cat b a
>   inverseMorphisms : InverseMorphisms cat a b morphism inverse
>
> buildIsomorphism :
>      {cat : Category}
>   -> {a, b : obj cat}
>   -> (morphism : mor cat a b)
>   -> (inverse : mor cat b a)
>   -> LeftInverse morphism inverse
>   -> RightInverse morphism inverse
>   -> Isomorphism cat a b morphism
> buildIsomorphism {cat} {a} {b} morphism inverse leftInverse rightInverse = MkIsomorphism
>   inverse
>   (MkInverseMorphisms leftInverse rightInverse)
>
> record Isomorphic (cat : Category) (a : obj cat) (b : obj cat) where
>   constructor MkIsomorphic
>   morphism : mor cat a b
>   isomorphism : Isomorphism cat a b morphism
>
> buildIsomorphic :
>      {cat : Category}
>   -> {a, b : obj cat}
>   -> (morphism : mor cat a b)
>   -> (inverse : mor cat b a)
>   -> LeftInverse morphism inverse
>   -> RightInverse morphism inverse
>   -> Isomorphic cat a b
> buildIsomorphic {cat} {a} {b} morphism inverse leftInverse rightInverse = MkIsomorphic
>   morphism
>   (buildIsomorphism morphism inverse leftInverse rightInverse)
>
> postulate
> isomorphicEq :
>      {cat : Category}
>   -> {a, b : obj cat}
>   -> (iso1, iso2 : Isomorphic cat a b)
>   -> (morphism iso1 = morphism iso2)
>   -> (inverse $ isomorphism iso1 = inverse $ isomorphism iso2)
>   -> iso1 = iso2
>
> idIsomorphic : {cat : Category} -> (a : obj cat) -> Isomorphic cat a a
> idIsomorphic {cat} a = buildIsomorphic
>   (identity cat a)
>   (identity cat a)
>   (leftIdentity cat a a (identity cat a))
>   (leftIdentity cat a a (identity cat a))
>
> isoMorphicComposition :
>      {cat : Category}
>   -> (a, b, c : obj cat)
>   -> Isomorphic cat a b
>   -> Isomorphic cat b c
>   -> Isomorphic cat a c
> isoMorphicComposition {cat} a b c iso1 iso2 = buildIsomorphic
>   (compose cat a b c (morphism iso1) (morphism iso2))
>   (compose cat c b a (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))
>   (trans (associativity cat a c b a _ (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))
>          (trans (cong2 (trans (sym (associativity cat a b c b (morphism iso1) (morphism iso2) (inverse $ isomorphism iso2)))
>                               (trans (cong (lawLeft $ inverseMorphisms $ isomorphism iso2))
>                                      (rightIdentity cat a b (morphism iso1))))
>                        (Refl { x = inverse $ isomorphism iso1 }))
>                 (lawLeft $ inverseMorphisms $ isomorphism iso1)))
>   (trans (associativity cat c a b c _ (morphism iso1) (morphism iso2))
>          (trans (cong2 (trans (sym (associativity cat c b a b (inverse $ isomorphism iso2) (inverse $ isomorphism iso1) (morphism iso1)))
>                               (trans (cong (lawRight $ inverseMorphisms $ isomorphism iso1))
>                                      (rightIdentity cat c b (inverse $ isomorphism iso2))))
>                        (Refl { x = morphism iso2 }))
>                 (lawRight $ inverseMorphisms $ isomorphism iso2)))
>
> isomorphicCategory : (cat : Category) -> Category
> isomorphicCategory cat = MkCategory
>   (obj cat)
>   (Isomorphic cat)
>   idIsomorphic
>   isoMorphicComposition
>   (\a, b, iso => isomorphicEq (isoMorphicComposition a a b (idIsomorphic a) iso) iso
>     (leftIdentity cat a b (morphism iso))
>     (rightIdentity cat b a (inverse $ isomorphism iso)))
>   (\a, b, iso => isomorphicEq (isoMorphicComposition a b b iso (idIsomorphic b)) iso
>     (rightIdentity cat a b (morphism iso))
>     (leftIdentity cat b a (inverse $ isomorphism iso)))
>   (\a, b, c, d, iso1, iso2, iso3 => isomorphicEq
>     (isoMorphicComposition a b d iso1 (isoMorphicComposition b c d iso2 iso3))
>     (isoMorphicComposition a c d (isoMorphicComposition a b c iso1 iso2) iso3)
>     (associativity cat a b c d (morphism iso1) (morphism iso2) (morphism iso3))
>     (sym (associativity cat d c b a (inverse $ isomorphism iso3) (inverse $ isomorphism iso2) (inverse $ isomorphism iso1))))
