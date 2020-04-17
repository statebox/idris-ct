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

> module Dual.DualCategory
>
> import Basic.Category
> import Basic.Functor
> import Basic.Isomorphism
> import Cats.CatsAsCategory
>
> %access public export
> %default total
>
> dualMorphism :
>      (cat : Category)
>   -> (a, b  : obj cat)
>   -> Type
> dualMorphism cat a b = mor cat b a
>
> dualCompose :
>      (cat : Category)
>   -> (a, b, c : obj cat)
>   -> (f : dualMorphism cat a b)
>   -> (g : dualMorphism cat b c)
>   -> dualMorphism cat a c
> dualCompose cat a b c f g = (compose cat) c b a g f
>
> dualAssoc :
>      (cat : Category)
>   -> (a, b, c, d : obj cat)
>   -> (f : dualMorphism cat a b)
>   -> (g : dualMorphism cat b c)
>   -> (h : dualMorphism cat c d)
>   ->  dualCompose cat a b d f (dualCompose cat b c d g h)
>       = dualCompose cat a c d (dualCompose cat a b c f g) h
> dualAssoc cat a b c d f g h = sym (associativity cat d c b a h g f)
>
> dualLeftIdentity :
>      (cat : Category)
>   -> (a, b : obj cat)
>   -> (f : dualMorphism cat a b)
>   -> dualCompose cat a a b (identity cat a) f = f
> dualLeftIdentity cat a b f = rightIdentity cat b a f
>
> dualRightIdentity :
>      (cat : Category)
>   -> (a, b : obj cat)
>   -> (f : dualMorphism cat a b)
>   -> dualCompose cat a b b f (identity cat b) = f
> dualRightIdentity cat a b f = leftIdentity cat b a f
>
> dualCategory : (cat : Category) -> Category
> dualCategory cat = MkCategory
>   (obj cat)
>   (dualMorphism cat)
>   (identity cat)
>   (dualCompose cat)
>   (dualLeftIdentity cat)
>   (dualRightIdentity cat)
>   (dualAssoc cat)
>
> doubleDualTo : (cat : Category) -> CFunctor (dualCategory $ dualCategory cat) cat
> doubleDualTo cat = MkCFunctor
>   id
>   (\_, _ => id)
>   (\_ => Refl)
>   (\_, _, _, _, _ => Refl)
>
> doubleDualFrom : (cat : Category) -> CFunctor cat (dualCategory $ dualCategory cat)
> doubleDualFrom cat = MkCFunctor
>   id
>   (\_, _ => id)
>   (\_ => Refl)
>   (\_, _, _, _, _ => Refl)
>
>
> doubleDualIsomorphism :
>      (cat : Category)
>   -> Isomorphic CatsAsCategory.catsAsCategory
>                  cat
>                  (dualCategory $ dualCategory cat)
> doubleDualIsomorphism cat = buildIsomorphic
>   (doubleDualFrom cat)
>   (doubleDualTo   cat)
>   (functorEq cat
>              cat
>              (functorComposition cat
>                                  (dualCategory $ dualCategory cat)
>                                  cat
>                                  (doubleDualFrom cat)
>                                  (doubleDualTo cat))
>              (idFunctor cat)
>              (\_ => Refl)
>              (\_, _, _ => Refl))
>   (functorEq (dualCategory $ dualCategory cat)
>              (dualCategory $ dualCategory cat)
>              (functorComposition (dualCategory $ dualCategory cat)
>                                  cat
>                                  (dualCategory $ dualCategory cat)
>                                  (doubleDualTo cat)
>                                  (doubleDualFrom cat))
>              (idFunctor (dualCategory $ dualCategory cat))
>              (\_ => Refl)
>              (\_, _, _ => Refl))
>
> dualPreservesIsomorphic :
>      Isomorphic (dualCategory cat) a b
>   -> Isomorphic cat a b
> dualPreservesIsomorphic
>   (MkIsomorphic
>     morphism
>     (MkIsomorphism inverse
>       (MkInverseMorphisms lawLeft lawRight))) =
>   MkIsomorphic
>     inverse
>     (MkIsomorphism
>       morphism
>       (MkInverseMorphisms lawLeft lawRight))
