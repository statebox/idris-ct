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
>
> %access public export
> %default total
>
> dualMorphism:
>      (cat : Category)
>   -> (a, b  : obj cat)
>   -> Type
> dualMorphism cat a b = mor cat b a
>
> dualCompose :
>      (cat : Category)
>   -> (a, b, c : obj cat)
>   -> (g : mor cat b a)
>   -> (f : mor cat c b)
>   -> mor cat c a
> dualCompose cat a b c g f = (compose cat) c b a f g
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
>   -> (a : obj cat)
>   -> (b : obj cat)
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
